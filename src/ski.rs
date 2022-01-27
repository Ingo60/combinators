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

use SKI::*;

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
    pub fn step(&self, n_max: usize) -> Self {
        let mut vs = Vec::new();
        self.unfolded(&mut vs);
        let mut n = 0;
        while n < n_max && SKI::evalstep(&mut vs) {
            n += 1;
        }
        SKI::folded(&mut vs)
    }

    /// returns true if the vector was changed
    fn evalstep(vs: &mut Vec<SKI>) -> bool {
        let some = vs.pop().unwrap();
        match some {
            S if vs.len() < 3 => {
                vs.push(S);
                return false;
            }
            K if vs.len() < 2 => {
                vs.push(K);
                return false;
            }
            I if vs.len() < 1 => {
                vs.push(I);
                return false;
            }
            S => {
                // Sfgx = fx(gx)
                let f = vs.pop().unwrap();
                let g = vs.pop().unwrap();
                let x = vs.pop().unwrap();
                vs.push(g.app(x.clone()));
                vs.push(x);
                vs.push(f);
            }
            K => {
                // Kab = a
                let a = vs.pop().unwrap();
                let _b = vs.pop();
                vs.push(a);
            }
            I => {
                // Ix = x  (but x is still on the stack, so we don't do anything)
            }
            app @ App(_, _) => {
                // I(ab)xy → (ab)xy → abxy
                app.unfolded(vs);
            }
            unknown => {
                vs.push(unknown);
                return false;
            }
        }
        return true;
    }

    pub fn eval(&self) -> Self {
        let mut vs = Vec::new();
        self.unfolded(&mut vs);
        let mut n_iter = 0;
        interruption::reset();
        while SKI::evalstep(&mut vs) {
            n_iter += 1;
            if n_iter % (1024 * 1024) == 0 && interruption::was_interrupted() {
                eprintln!("\x08\x08aborted");
                break;
            }
        }
        SKI::folded(&mut vs)
    }

    pub fn folded(vs: &mut Vec<SKI>) -> Self {
        assert!(vs.len() > 0);
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
}

pub fn is_comb(c: char) -> bool {
    c.is_uppercase() || c.is_numeric()
}

pub fn atom() -> GenericP<u8, SKI, String> {
    spaces().then(
        (expect('S').map(|_| S))
            .or(expect('K').map(|_| K))
            .or(expect('I').map(|_| I))
            .or(satisfy(is_comb).map(|c| Comb(c.to_string())))
            .or(expect('[')
                .then(take(|c| c != ']'))
                .before(expect(']'))
                .map(|s| Comb(s)))
            .or(satisfy(|c| c.is_lowercase()).map(|c| Var(c)))
            .label("variable or combinator expected"),
    )
}

pub fn term() -> GenericP<u8, SKI, String> {
    spaces().then(
        atom().or(expect('(')
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
