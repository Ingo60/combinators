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
    PC,
    PN,
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
            PN => write!(f, "#"),
            PC => write!(f, "."),
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
        while n < n_max && SKI::evalstep(&mut vs, hash, false) {
            n += 1;
        }
        SKI::folded(&mut vs)
    }

    /// returns true if the vector was changed
    fn evalstep(vs: &mut Vec<SKI>, hash: &HashMap<String, SKI>, side_effects: bool) -> bool {
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
            I | PC | PN if n_args < 1 => {
                vs.push(some);
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
            PC | PN if !side_effects => {
                vs.pop().unwrap();
                vs.push(I);
                true
            }
            PN => {
                let mut n = vs.pop().unwrap().eval(hash);
                vs.push(I);
                let mut v = 0u64;
                let y = hash.get("zero?").map(|x| x.eval(hash)).and_then(|z| {
                    hash.get("pred").map(|x| x.eval(hash)).and_then(|p| {
                        loop {
                            let is_0 = z.clone().app(n.clone()).eval(hash);
                            if is_0 == K.app(I) {
                                v += 1;
                                n = p.clone().app(n.clone());
                            } else if is_0 == K {
                                print!("{}", v);
                                break;
                            } else {
                                eprintln!("{}{} is not a number{}", YELLOW, n.clone(), NORMAL);
                                break;
                            }
                        }
                        Some(S)
                    })
                });
                if y.is_none() {
                    eprintln!("{}[pred] or [zero?] are not defined.{}", YELLOW, NORMAL);
                }
                /*
                 */
                true
            }
            app @ App(_, _) => {
                // I(ab)xy ??? (ab)xy ??? abxy
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
        while SKI::evalstep(&mut vs, hash, true) {
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

    /// ab(cd) ??? [cd, b, a]
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

    /// checks if expression contains variable [v]
    pub fn has_var(&self, v: char) -> bool {
        match self {
            S | K | I | PC | PN | Comb(_) => false,
            Var(x) => v.eq(x),
            App(a, b) => a.has_var(v) || b.has_var(v),
        }
    }

    /// check if expression contains combinator [name]
    pub fn has_comb(&self, name: &str) -> bool {
        match self {
            S | K | I | PC | PN | Var(_) => false,
            Comb(x) => x.eq(&name),
            App(a, b) => a.has_comb(name) || b.has_comb(name),
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
                Var(x) if v == x && !a.has_var(v) => a.as_ref().clone(), /* by rule 3 */
                _b if !self.has_var(v) => K.app(self.clone()),           /* by rule 2 */
                b => S.app(a.eliminate(v)).app(b.eliminate(v)),          /* by rule 4 */
            },
            // self is not a variable and not of the form xy
            // This means that v cannot occur in it, hence rule 2
            other => K.app(other),
        }
    }

    /// checks if SKI expression is just a variable
    pub fn is_var(&self) -> bool {
        if let Var(_) = self {
            true
        } else {
            false
        }
    }

    /// checks if SKI consists only of vars applied to each other
    pub fn is_varapp(&self) -> bool {
        match self {
            Var(_) => true,
            App(a, b) => b.is_var() && a.is_varapp(),
            _ => false,
        }
    }
}

/// tell if this character can be the name of a combinator
pub fn is_comb(c: char) -> bool {
    c.is_uppercase() || c.is_numeric() || c == '_'
}

/// Construct a parser that parses combinators
pub fn p_comb() -> GenericP<u8, SKI, String> {
    let single = satisfy(is_comb).map(|c| Comb(c.to_string()));
    let charcode = expect('\'')
        .commit()
        .then(satisfy(|_| true).label("character to encode"))
        .before(expect('\''))
        .map(|c| Comb(format!("{}", c as u32)));
    let brackets = expect('[')
        .commit()
        .then(take(|c| c != ']').label("type constructor name").guard(
            |name| name != "S" && name != "K" && name != "I" && name != "#" && name != ".",
            |name| format!("\"{}\" is a reserved constructor name", name),
        ))
        .before(expect(']'))
        .map(Comb);
    brackets
        .or(charcode)
        .or(single.label("combinator expected"))
}

#[test]
pub fn test_p_comb() {
    for text in ["", "[", "[x", "[x]"] {
        print!("text={:<8}", format!("\"{text}\""));
        println!("p_comb {:?}", p_comb().parse_str_raw(text));
        print!("text={:<8}", format!("\"{text}\""));
        println!("p_atom {:?}", p_atom().parse_str_raw(text));
        print!("text={:<8}", format!("\"{text}\""));
        println!("p_term {:?}", p_term().parse_str_raw(text));
    }
}

pub fn p_atom() -> GenericP<u8, SKI, String> {
    spaces().then(
        (satisfy(|c| c == 'S' || c == 'K' || c == 'I' || c == '#' || c == '.').map(|c| match c {
            'S' => S,
            'K' => K,
            'I' => I,
            '#' => PN,
            '.' => PC,
            _ => panic!("satisfy {}?", c),
        }))
        .or(p_comb())
        .or(satisfy(|c| c.is_lowercase())
            .map(Var)
            .label("variable or combinator expected")),
    )
}

pub fn p_term() -> GenericP<u8, SKI, String> {
    (spaces()
        .then(expect('('))
        .label("SKI term expected")
        .commit()
        .and_then(|_| p_expr())
        .before(spaces().then(expect(')'))))
    .or(p_atom())
}

pub fn p_expr() -> GenericP<u8, SKI, String> {
    p_term()
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
        "(S  ??  \r\nK????) I",
        "SIII(((((I)))))(KS)(KS)(KS)    ",
        "((((((((((((((((((((((((((((S))))))))))))))))))))))))))",
        "(KK)(KKK)(KKKK)(KKKKK)(KKKKKKK)(KKKKKKKK)",
        "(This) (is) (nice)",
    ] {
        print!("text \"{}\"   ", text);
        match p_expr()
            .before(spaces().then(end_of_input()))
            .parse_str(text)
        {
            Ok(v) => println!("{}", v),
            Err(e) => println!("{}", e),
        }
    }
}
