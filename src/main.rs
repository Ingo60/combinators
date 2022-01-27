// use super::ski;

use combinators::interruption;
use combinators::parser::{end_of_input, spaces, StrParser};
use combinators::ski::expr;
use rustyline::completion::Completer;
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::validate::Validator;
use rustyline::{Config, Editor, Helper};
use std::env;

pub const RED: &str = "\x1b\x5b31m";
pub const YELLOW: &str = "\x1b\x5b32m";
pub const BLUE: &str = "\x1b\x5b34m";
pub const NORMAL: &str = "\x1b\x5b0m";

pub fn main() {
    let hist_file = (env::var("HOME").and_then(|home| Ok(format!("{}/.comb_history", home))))
        .or::<env::VarError>(Ok(".comb_history".to_string()))
        .unwrap();
    let config = Config::builder().auto_add_history(true).build();
    // `()` can be used when no completer is required
    let mut rl = Editor::<SkiHelper>::with_config(config);
    rl.set_helper(Some(SkiHelper {}));
    if rl.load_history(&hist_file).is_err() {
        println!("No previous history in {}", hist_file);
    }
    interruption::initialize();
    loop {
        let readline = rl.readline("⌦ ");
        match readline {
            Ok(line) => match expr()
                .before(spaces().then(end_of_input()))
                .parse_str(&line)
            {
                Ok(v) => println!("{}", v.eval().un_i()),
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

struct SkiHelper {}

impl Helper for SkiHelper {}

impl Completer for SkiHelper {
    type Candidate = String;
}

impl Validator for SkiHelper {}

impl Hinter for SkiHelper {
    type Hint = String;

    fn hint(&self, line: &str, _pos: usize, _ctx: &rustyline::Context<'_>) -> Option<Self::Hint> {
        match expr()
            .before(spaces().then(end_of_input()))
            .parse_str(&line)
        {
            Ok(ski) => Some(format!("{} → {}{}", BLUE, ski.step(128).un_i(), NORMAL)),
            Err(_) => None,
        }
    }
}

impl Highlighter for SkiHelper {
    fn highlight<'l>(&self, line: &'l str, _pos: usize) -> std::borrow::Cow<'l, str> {
        match expr()
            .before(spaces().then(end_of_input()))
            .parse_str_raw(&line)
        {
            (u, Err(_)) if u > 0 && u < line.len() && line.is_char_boundary(u) => {
                let (a, b) = line.split_at(u);
                let c = a.to_string() + RED + b + NORMAL;
                std::borrow::Cow::from(c.clone())
            }
            _other => std::borrow::Cow::Borrowed(line),
        }
    }
    fn highlight_char(&self, line: &str, _pos: usize) -> bool {
        match expr()
            .before(spaces().then(end_of_input()))
            .parse_str_raw(&line)
        {
            (u, Err(_)) if u > 0 && u < line.len() && line.is_char_boundary(u) => true,
            _other => false,
        }
    }
}
