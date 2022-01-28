use std::collections::HashMap;

use super::interruption;
use super::parser::*;

use std::fmt;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SKI {
    S,
    K,
    I,
    /// variable
    Var(char),
    /// combinator
    Comb(String),
    App(Rc<SKI>, Rc<SKI>),
}

pub use SKI::*;

impl fmt::Display for SKI {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            S => write!(f, "S"),
            K => write!(f, "K"),
            I => write!(f, "I"),
            Var(c) => write!(f, "{}", c),
            Comb(name) => {
                let mut iter = name.chars();
                if iter.next().map(is_comb) == Some(true) && iter.next().is_none() {
                    write!(f, "{}", name)
                } else {
                    write!(f, "[{}]", name)
                }
            }
            App(a, b) => {
                a.fmt(f)?;
                if let App(_, _) = b.as_ref() {
                    write!(f, "(")?;
                    b.fmt(f)?;
                    write!(f, ")")
                } else {
                    b.fmt(f)
                }
            }
        }
    }
}

impl SKI {
    /// create an application
    pub fn app(self, other: SKI) -> Self {
        App(Rc::new(self), Rc::new(other))
    }

    /// beautify expression by removing applications of I
    pub fn un_i(&self) -> Self {
        if let App(a, b) = self.clone() {
            let left = a.un_i();
            let right = b.un_i();
            if left == I {
                right
            } else {
                left.app(right)
            }
        } else {
            self.clone()
        }
    }
    /// Do at most n evaluation steps
    pub fn step(&self, n_max: usize, hash: &HashMap<String, SKI>) -> Self {
        let mut vs = Vec::new();
        self.unfolded(&mut vs);
        let mut n = 0;
        while n < n_max && SKI::evalstep(&mut vs, hash) {
            n += 1;
        }
        SKI::folded(&mut vs)
    }

    /// returns true if the vector was changed
    fn evalstep(vs: &mut Vec<SKI>, hash: &HashMap<String, SKI>) -> bool {
        let some = vs.pop().unwrap();
        let n_args = vs.len();
        match some {
            S if n_args < 3 => {
                vs.push(S);
                false
            }
            K if n_args < 2 => {
                vs.push(K);
                false
            }
            I if n_args < 1 => {
                vs.push(I);
                false
            }
            S => {
                // Sfgx = fx(gx)
                let f = vs.pop().unwrap();
                let g = vs.pop().unwrap();
                let x = vs.pop().unwrap();
                vs.push(g.app(x.clone()));
                vs.push(x);
                vs.push(f);
                true
            }
            K => {
                // Kab = a
                let a = vs.pop().unwrap();
                let _b = vs.pop();
                vs.push(a);
                true
            }
            I => {
                // Ix = x  (but x is still on the stack, so we don't do anything)
                true
            }
            app @ App(_, _) => {
                // I(ab)xy → (ab)xy → abxy
                app.unfolded(vs);
                true
            }
            Comb(name) => match hash.get(&name) {
                Some(s) => {
                    s.unfolded(vs);
                    true
                }
                None => {
                    vs.push(Comb(name));
                    false
                }
            },
            unknown => {
                vs.push(unknown);
                false
            }
        }
    }

    pub fn eval(&self, hash: &HashMap<String, SKI>) -> Self {
        let mut vs = Vec::new();
        self.unfolded(&mut vs);
        let mut n_iter = 0;
        interruption::reset();
        while SKI::evalstep(&mut vs, hash) {
            n_iter += 1;
            if n_iter % (1024 * 1024) == 0 && interruption::was_interrupted() {
                eprintln!("\x08\x08aborted");
                break;
            }
        }
        SKI::folded(&mut vs)
    }

    pub fn folded(vs: &mut Vec<SKI>) -> Self {
        assert!(!vs.is_empty());
        let mut some_a = vs.pop();
        while let Some(b) = vs.pop() {
            some_a = some_a.map(|a| a.app(b));
        }
        some_a.unwrap() // safe because justified assertion above
    }

    /// ab(cd) → [cd, b, a]
    pub fn unfolded(&self, vs: &mut Vec<SKI>) {
        match self.clone() {
            App(a, b) => {
                let ski = b.as_ref();
                vs.push(ski.clone());
                a.unfolded(vs);
            }
            it => vs.push(it),
        }
    }

    /// substitute default placeholder with given SKI
    pub fn subst_default(&self, s: SKI) -> Self {
        match self.clone() {
            Comb(name) if name == "_" => s,
            App(a, b) => a.subst_default(s.clone()).app(b.subst_default(s)),
            ski => ski,
        }
    }

    /// checks if expression contains variable 'v'
    pub fn has(&self, v: char) -> bool {
        match self {
            S | K | I | Comb(_) => false,
            Var(x) => v.eq(x),
            App(a, b) => a.has(v) || b.has(v),
        }
    }

    /// `x.eliminate(v)` computes an expression `y` that does not contain `v` such that `yv` evaluates to `x`
    ///
    /// # Elimination rules
    ///
    /// 1. `v.eliminate(v) = I` because `Iv = v`
    /// 2. `x.eliminate(v) = Kx` if x does not contain v, because `Kxv = x`
    /// 3. `(xv).eliminate(v) = x` if x does not contain v, because `xv = xv`
    /// 4. `(ab).eliminate(v) = Scd` where `c = a.eliminate(v)` and `d=b.eliminate(v)`. Because `Scdv = cv(dv)` and `cv = a`
    /// (by definition) and `dv = b` (by definition), `cv(dv) = ab`
    pub fn eliminate(&self, v: char) -> Self {
        match self.clone() {
            Var(x) => {
                if v == x {
                    I /* by rule 1 */
                } else {
                    K.app(Var(x)) /* by rule 2 */
                }
            }
            App(a, b) => match b.as_ref().clone() {
                Var(x) if v == x && !a.has(v) => a.as_ref().clone(), /* by rule 3 */
                _b if !self.has(v) => K.app(self.clone()),           /* by rule 2 */
                b => S.app(a.eliminate(v)).app(b.eliminate(v)),      /* by rule 4 */
            },
            // self is not a variable and not of the form xy
            // This means that v cannot occur in it, hence rule 2
            other => K.app(other),
        }
    }
}

/// tell if this character can be the name of a combinator
pub fn is_comb(c: char) -> bool {
    c.is_uppercase() || c.is_numeric() || c == '_'
}

pub fn atom() -> GenericP<u8, SKI, String> {
    spaces().then(
        (expect('S').map(|_| S))
            .or(expect('K').map(|_| K))
            .or(expect('I').map(|_| I))
            .or(satisfy(is_comb).map(|c| Comb(c.to_string())))
            .or(expect('[')
                .then(
                    take(|c| c != ']')
                        .guard(|name| name != "S" && name != "K" && name != "V")
                        .label("forbidden constructor name"),
                )
                .before(expect(']'))
                .map(Comb))
            .or(satisfy(|c| c.is_lowercase()).map(Var))
            .label("variable or combinator expected"),
    )
}

pub fn term() -> GenericP<u8, SKI, String> {
    spaces().then(
        atom().or(expect('(')
            .label("SKI term expected")
            .and_then(|_| expr())
            .before(spaces().then(expect(')')))),
    )
}

pub fn expr() -> GenericP<u8, SKI, String> {
    term()
        .some()
        .map(|vs| vs.iter().cloned().reduce(|a, b| a.app(b)).unwrap())
    // .label("SKI term expected")
}

#[test]
pub fn parse_test() {
    for text in [
        " ",
        "S",
        "K",
        "2+2=4",
        "(S  Æ  \r\nKæØ) I",
        "SIII(((((I)))))(KS)(KS)(KS)    ",
        "((((((((((((((((((((((((((((S))))))))))))))))))))))))))",
        "(KK)(KKK)(KKKK)(KKKKK)(KKKKKKK)(KKKKKKKK)",
        "(This) (is) (nice)",
    ] {
        print!("text \"{}\"   ", text);
        match expr().before(spaces().then(end_of_input())).parse_str(text) {
            Ok(v) => println!("{}", v),
            Err(e) => println!("{}", e),
        }
    }
}
