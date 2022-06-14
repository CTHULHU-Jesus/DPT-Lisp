// IMPORTS
#[path = "lib.rs"]
mod lib;
use lib::Context;
use lib::{repl_to_span, State};
use std::fs::{read_to_string, OpenOptions};
use Box;

use anyhow::Result;
use clap::Parser;
// use lib::EvalResult;
// use lib::State;
use rustyline;
use rustyline::error::ReadlineError;
use rustyline::Editor;
// CONSTS
const HISTORY: &'static str = "lispr-history.txt";
// TYPES

#[derive(Parser, Debug)]
#[clap(about, version, author)]
struct Args {
  /// Only check if files parse, do not run them.
  #[clap(short, long)]
  pub parse_check: bool,

  /// Only check if files type check, do not run them.
  #[clap(short, long)]
  pub type_check: bool,

  /// Drop into a readline prompt after loading files.
  #[clap(short, long)]
  pub readline_mode: bool,

  /// Files to load and run.
  pub files: Vec<String>,
}
// FUNCTIONS

// /// print a result
// fn print_eval_result(r: EvalResult) {
//   match r {
//     Val(v) => println!("{}", v),
//     Error(e) => eprintln!("Error: {}", e),
//   }
// }

/// main loop
fn main() -> Result<()> {
  let args = Args::parse();
  // decide what to do with the files
  let mut state = State::default();
  let mut context = Context::default();
  if args.parse_check {
    let out = lib::parse_files(&(args.files))?;
    for expr in out {
      println!("{expr}");
    }
    return Ok(());
  } else if args.type_check {
    lib::type_check_files(&(args.files), &mut context)?;
    return Ok(());
  } else {
    let out = lib::run(&(args.files), &mut state)?;
    // println!("{out:#?}");

    if args.readline_mode {
      // readline mode
      readline_mode(&mut state)?
    }
  };

  // return
  Ok(())
}

/// Creates a file if it doesn't exist
fn create_file(path: &str) -> Result<()> {
  let _file = OpenOptions::new().write(true).create(true).open(path)?;
  Ok(())
}

/// readline loop
fn readline_mode(state: &mut State) -> Result<()> {
  let mut rl = Editor::<()>::new();
  create_file(HISTORY)?;
  if rl.load_history(HISTORY).is_err() {
    println!("No history found.");
  }

  loop {
    let input = rl.readline("lisp> ");

    match input {
      core::result::Result::Ok(line) => {
        rl.add_history_entry(line.as_str());
        // exit check
        if line.trim() == "error" {
          break;
        }
        // let extra = format!("REPL input {line}");
        let span = repl_to_span(&line); //::Span::new_extra(line.as_str(), extra.as_str());
        let out = lib::run1(&span, state);
        match out {
          Err(e) => println!("{e}"),
          Ok(x) => println!("{x}"),
        }
      }
      Err(ReadlineError::Interrupted) => {
        println!("CTRL-C");
        break;
      }
      Err(ReadlineError::Eof) => {
        println!("CTRL-D");
        break;
      }
      Err(err) => {
        eprintln!("Error: {:?}", err);
        break;
      }
    }
  }
  rl.save_history(HISTORY)?;
  Ok(())
}
// TRAITS
// IMPLS
// TESTS
