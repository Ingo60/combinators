// use super::ski;

use combinators::interpreter::{p_command, Command::*, Interpreter};
use combinators::interruption;
use combinators::parser::{end_of_input, spaces, StrParser};
use rustyline::completion::Completer;
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use rustyline::{Config, Editor, Helper};
use std::{env, ops::DerefMut};

pub const RED: &str = "\x1b\x5b31m";
pub const YELLOW: &str = "\x1b\x5b32m";
pub const BLUE: &str = "\x1b\x5b34m";
pub const NORMAL: &str = "\x1b\x5b0m";

pub fn main() {
    let hist_file = (env::var("HOME").map(|home| format!("{}/.comb_history", home)))
        .or_else::<env::VarError, _>(|_| Ok(".comb_history".to_string()))
        .unwrap();
    let config = Config::builder().auto_add_history(true).build();
    // `()` can be used when no completer is required
    let mut rl = Editor::<SkiHelper>::with_config(config);
    let mut inter = Box::new(Interpreter::new());
    let mut ski_helper = SkiHelper {
        inter: inter.clone(),
    };

    if rl.load_history(&hist_file).is_err() {
        println!("No previous history in {}", hist_file);
    }
    interruption::initialize();
    loop {
        rl.set_helper(Some(ski_helper.clone()));
        let readline = rl.readline("⌦ ");
        match readline {
            Ok(line) => match p_command()
                .before(spaces().then(end_of_input()))
                .parse_str(&line)
            {
                Ok(cmd) => {
                    inter.deref_mut().execute(cmd);
                    ski_helper.update_inter(inter.clone());
                }
                Err(e) => println!("{}{}{}", RED, e, NORMAL),
            },
            Err(ReadlineError::Interrupted) => {
                println!("CTRL-C");
                break;
            }
            Err(ReadlineError::Eof) => {
                println!("CTRL-D");
                break;
            }
            Err(err) => {
                println!("Error: {:?}", err);
                break;
            }
        }
    }
    rl.save_history(&hist_file).unwrap();
}

#[derive(Clone)]
struct SkiHelper {
    inter: Box<Interpreter>,
}

impl SkiHelper {
    pub fn update_inter(&mut self, n: Box<Interpreter>) {
        self.inter = n;
    }
}

impl Helper for SkiHelper {}

impl Completer for SkiHelper {
    type Candidate = String;
}

impl Validator for SkiHelper {}

impl Hinter for SkiHelper {
    type Hint = String;

    fn hint(&self, line: &str, _pos: usize, _ctx: &rustyline::Context<'_>) -> Option<Self::Hint> {
        match p_command()
            .before(spaces().then(end_of_input()))
            .parse_str(line)
        {
            Ok(Eval(ski)) => Some(format!(
                "{} → {}{}",
                BLUE,
                ski.subst_default(self.inter.last.clone())
                    .step(128, &self.inter.env)
                    .un_i(),
                NORMAL
            )),
            Ok(Step(ski)) => Some(format!(
                "{}  →  {}{}",
                BLUE,
                ski.subst_default(self.inter.last.clone())
                    .step(128, &self.inter.env)
                    .un_i(),
                NORMAL
            )),
            Ok(Let(_, ski)) => Some(format!(
                "{} → {}{}",
                BLUE,
                ski.subst_default(self.inter.last.clone())
                    .step(128, &self.inter.env)
                    .un_i(),
                NORMAL
            )),
            Err(s) => Some(format!("     {}{}{}", RED, s, NORMAL)),
        }
    }
}

impl Highlighter for SkiHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> std::borrow::Cow<'l, str> {
        match p_command()
            .before(spaces().then(end_of_input()))
            .parse_str_raw(line)
        {
            (u, Err(_)) if u < line.len() && line.is_char_boundary(u) => {
                let (a, b) = line.split_at(u);
                let c = a.to_string() + RED + b + NORMAL;
                std::borrow::Cow::from(c)
            }
            _other => std::borrow::Cow::Borrowed(line),
        }
    }
    fn highlight_char(&self, line: &str, _pos: usize) -> bool {
        match p_command()
            .before(spaces().then(end_of_input()))
            .parse_str_raw(line)
        {
            (u, Err(_)) => u < line.len() && line.is_char_boundary(u),
            _other => false,
        }
    }
}
