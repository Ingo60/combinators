//! SKI interpreter

use crate::parser::{NORMAL, YELLOW};

use super::parser::{end_of_input, expect, spaces, GenericP};
use super::ski;
use super::ski::{App, Comb, Var, I, K, S, SKI};

use std::collections::{HashMap, HashSet};

#[derive(Clone)]
pub struct Interpreter {
    pub last: SKI,
    pub env: HashMap<String, SKI>,
}

impl Default for Interpreter {
    fn default() -> Self {
        Interpreter::new()
    }
}

impl Interpreter {
    pub fn new() -> Self {
        let hash = HashMap::new();
        Interpreter { last: I, env: hash }
    }

    pub fn execute(&mut self, cmd: Command) {
        match cmd {
            Eval(ski) => {
                let current = ski.subst_default(self.last.clone()).eval(&self.env).un_i();
                println!("{}", current);
                self.last = current;
            }
            Step(ski) => {
                let current = ski
                    .subst_default(self.last.clone())
                    .step(1, &self.env)
                    .un_i();
                println!("{}", current);
                self.last = current;
            }
            Let(left, right) => {
                let mut vars = HashSet::new();
                let undefault = right.subst_default(self.last.clone());
                match def(left, undefault, &mut vars, &self.env) {
                    Ok((name, ski)) => {
                        let uni = ski.un_i();
                        println!("{} = {}", Comb(name.clone()), uni);
                        self.env.insert(name.clone(), uni);
                        self.last = Comb(name);
                    }
                    Err(e) => eprintln!("{}{}{}", YELLOW, e, NORMAL),
                }
            }
        };
    }
}

fn def(
    left: SKI,
    right: SKI,
    vars: &mut HashSet<char>,
    env: &HashMap<String, SKI>,
) -> Result<(String, SKI), String> {
    let name = check_lhs(left.clone(), vars, env)?;
    check_free_vars(right.clone(), vars)?;
    let rhs = elim(left, right.un_i());
    Ok((name, rhs.un_i()))
}


fn elim(lhs: SKI, rhs: SKI) -> SKI {
    match lhs.clone() {
        Comb(_) => rhs,
        App(a, b) => match b.as_ref() { 
            Var(c) => elim(a.as_ref().clone(), rhs.eliminate(*c)), 
            _ => panic!("elim {} {}", lhs, rhs),
        }
        // anything else is not well formed
        _ => panic!("elim {} {}", lhs, rhs),
    }
}
fn check_free_vars(rhs: SKI, bound: &HashSet<char>) -> Result<(), String> {
    match rhs {
        S|K|I|Comb(_) => Ok(()),
        Var(v) if bound.contains(&v) => Ok(()),
        App(a,b) => check_free_vars(a.as_ref().clone(), bound).and_then(|_| check_free_vars(b.as_ref().clone(), bound)),
        Var(x) => Err(format!("Right hand side of definition must not contain free variable '{}'", x))
    }
}

fn check_lhs(lhs: SKI, vars: &mut HashSet<char>, env: &HashMap<String, SKI>) -> Result<String, String> {
    match lhs {
        Comb(name) if env.contains_key(&name) => 
            Err(format!("{} already defined, please :undef first", Comb(name))),
        Comb(name) => Ok(name),
        App(a,varb) => match varb.as_ref().clone() {
            Var(b) => check_lhs(a.as_ref().clone(), vars, env).and_then(|result|
                if vars.contains(&b) {
                    Err(format!("variable '{}' used more than once. The left hand side of a definition\n\
                                 must be an application of a new constructor to some unique variables, like Ffgx", b))}
                else { 
                    vars.insert(b);
                    Ok(result)
                }
            ),
            x => Err(format!("construct ({}) is not allowed on the left hand side of a definition.\n\
                                  It must be an application of a new constructor to some unique variables, like Ffgx", x)),},
        x => Err(format!("construct ({}) is not allowed on the left hand side of a definition.\n\
                              It must be an application of a new constructor to some unique variables, like Ffgx", x)),
        
    }
}

pub enum Command {
    Eval(SKI),
    Step(SKI),
    Let(SKI, SKI),
}

pub use Command::*;
pub fn p_command() -> GenericP<u8, Command, String> {
    let empty_line = end_of_input().map(|_| Step(Comb("_".to_string())));
    let eval_default = expect('?')
        .then(end_of_input())
        .map(|_| Eval(Comb("_".to_string())));
    spaces().then(
        empty_line
            .or(eval_default)
            .or(ski::expr().before(spaces()).and_then(|ski| {
                let ski_a = ski.clone();
                let ski_b = ski.clone();
                let ski_c = ski;
                expect('?')
                    .map(move |_| Eval(ski_a.clone()))
                    .or(end_of_input().map(move |()| Step(ski_b.clone())))
                    .or(expect('=').before(spaces()).then(ski::expr().before(spaces())).map(move |x| Let(ski_c.clone(),x)))
            })),
    )
}
