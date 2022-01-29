//! SKI interpreter

use crate::parser::{fail, skip, StrParser};

pub const RED: &str = "\x1b\x5b31m";
pub const BLUE: &str = "\x1b\x5b34m";

use super::parser::{end_of_input, expect, pure, spaces, take, GenericP, NORMAL, YELLOW};
use super::ski;
use super::ski::{p_comb, App, Comb, Var, I, K, S, SKI};

use std::{
    collections::{HashMap, HashSet},
    fs::File,
    io::{BufRead, BufReader},
};

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
            Help => {
                //        --------------------------------------------------------------------------
                println!("Commands:");
                println!("  :help            print this text");
                println!("  :list            list all known combinators and their definitions");
                println!("  :list C          list definition of combinator C");
                println!("  :load filename   load definitions in the named file");
                println!("  :echo text       print text on standard output");
                println!("  expr             perform 1 reduction on expr");
                println!("  expr?            evaluate expr until no more reductions are possible");
                println!("  expr = expr      define a combinator");
                println!("                   The left hand side must be a (new) combinator");
                println!("                   name applied to a number of different variables.");
                println!("                   The right hand side must not contain variables not");
                println!("                   introduced on the left hand side.");
                println!("");
                println!("Syntax of expresions:");
                println!("    Variable: single lowercase letter");
                println!("    Combinator: single uppercase letter or digit or arbitrary characters enclosed in []");
                println!("    Term: Variable | Combinator | (Expression)");
                println!("    Expression: Term | Expression Term");
                println!(
                    "  Note that `FGH` is the same as `(FG)H` and quite different from `F(GH)`"
                );
                println!("Conveniences:");
                println!(
                    "  The pseudo combinator _ can be used for the last evaluated expression."
                );
                println!("  An empty line evaluates _ one step further.");
            }
            Eval(ski) => {
                let current = ski.subst_default(self.last.clone()).eval(&self.env).un_i();
                let varonly = current.is_varapp();
                println!("{}", current);
                self.last = current;
                if varonly {
                    eprintln!(
                        "{}To enter a command, start the line with ':'{}",
                        YELLOW, NORMAL
                    );
                };
            }
            Step(ski) => {
                let current = ski
                    .subst_default(self.last.clone())
                    .step(1, &self.env)
                    .un_i();

                let varonly = current.is_varapp();

                println!("{}", current);
                self.last = current;
                if varonly {
                    eprintln!(
                        "{}To enter a command, start the line with ':'{}",
                        YELLOW, NORMAL
                    );
                };
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
            ListAll => {
                for kv in &self.env {
                    println!("{} = {}", Comb(kv.0.clone()), kv.1);
                }
            }
            List(name) => match self.env.get(&name) {
                Some(ski) => println!("{} = {}", Comb(name), ski),
                None => {
                    eprintln!("{}combinator not defined: {}{}", YELLOW, Comb(name), NORMAL)
                }
            },
            Load(path) => {
                let mut n_line = 0;
                match File::open(&path) {
                    Err(ioe) => {
                        eprintln!("{}could not open file {} ({}){}", YELLOW, path, ioe, NORMAL)
                    }
                    Ok(f) => {
                        for ok_line in BufReader::new(f).lines() {
                            if let Ok(line) = ok_line {
                                n_line += 1;
                                match p_command().parse_str(&line) {
                                    Ok(cmd) => self.execute(cmd),
                                    Err(e) => eprintln!(
                                        "line {}:{}{}{}\nerror: {}{}{}",
                                        n_line, YELLOW, line, NORMAL, RED, e, NORMAL,
                                    ),
                                }
                            }
                        }
                    }
                };
            }
            Echo(text) => println!("{}{}{}", BLUE, text, NORMAL),
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
        },
        // anything else is not well formed
        _ => panic!("elim {} {}", lhs, rhs),
    }
}
fn check_free_vars(rhs: SKI, bound: &HashSet<char>) -> Result<(), String> {
    match rhs {
        S | K | I | Comb(_) => Ok(()),
        Var(v) if bound.contains(&v) => Ok(()),
        App(a, b) => check_free_vars(a.as_ref().clone(), bound)
            .and_then(|_| check_free_vars(b.as_ref().clone(), bound)),
        Var(x) => Err(format!(
            "Right hand side of definition must not contain free variable '{}'",
            x
        )),
    }
}

fn check_lhs(
    lhs: SKI,
    vars: &mut HashSet<char>,
    env: &HashMap<String, SKI>,
) -> Result<String, String> {
    match lhs {
        // Comb(name) if env.contains_key(&name) =>
        //    Err(format!("{} already defined, please :undef first", Comb(name))),
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

#[derive(Clone)]
pub enum Command {
    Eval(SKI),
    Step(SKI),
    Let(SKI, SKI),
    ListAll,
    List(String),
    Help,
    Load(String),
    Echo(String),
}

pub use Command::*;
pub fn p_command() -> GenericP<u8, Command, String> {
    let comment = expect('-').then(expect('-')).then(skip(|_| true));
    let end_of_line = spaces().then(comment.optional()).then(end_of_input());
    let empty_line = end_of_line.map(|_| Step(Comb("_".to_string())));
    let eval_default = expect('?').map(|_| Eval(Comb("_".to_string())));
    let command = take(|c| c.is_alphabetic())
        .before(spaces())
        .label("enter command")
        .and_then(|s| match s.as_str() {
            "help" => pure(true).map(|_| Help),
            "list" => p_comb().optional().map(|r| match r {
                Some(Comb(n)) => List(n),
                _ => ListAll,
            }),
            "load" => take(|c| !c.is_whitespace())
                .label("expecting filename")
                .map(Load),
            "echo" => take(|_c| true).label("type some text").map(Echo),
            _ => fail("valid commands are help, list, load, save, echo"),
        });
    spaces()
        .then(
            (expect(':').commit().then(spaces()).then(command))
                .or(empty_line)
                .or(eval_default)
                .or(ski::p_expr().before(spaces()).and_then(move |ski| {
                    let ski_a = ski.clone();
                    let ski_b = ski.clone();
                    let ski_c = ski;
                    expect('?')
                        .map(move |_| Eval(ski_a.clone()))
                        .or(expect('=')
                            .then(spaces())
                            .then(ski::p_expr())
                            .map(move |x| Let(ski_c.clone(), x)))
                        .or(pure(42).map(move |_| Step(ski_b.clone())))
                })),
        )
        .before(end_of_line)
}
