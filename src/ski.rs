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
    Comb(char),
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
            Comb(c) => write!(f, "{}", c),
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

pub fn atom() -> GenericP<u8, SKI, String> {
    spaces().then(
        (expect('S').map(|_| S))
            .or(expect('K').map(|_| K))
            .or(expect('I').map(|_| I))
            .or(satisfy(|c| c.is_uppercase() || c.is_numeric()).map(|c| Comb(c)))
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
    let without_separator = pure(false);
    term().some(without_separator).map(|vs| {
        vs.iter()
            .cloned()
            .reduce(|a, b| App(Rc::new(a), Rc::new(b)))
            .unwrap()
    })
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
