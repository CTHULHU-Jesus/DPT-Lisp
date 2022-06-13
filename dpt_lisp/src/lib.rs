// IMPORTS

// project imports
#[path = "parse.rs"]
pub mod Parse;
use Parse::{LBuiltinF, LFunction, Value, AST};

#[path = "error.rs"]
pub mod Error;
pub use Error::{ErrorKind, FileLocation, MyError};

#[path = "builtin.rs"]
pub mod Builtin;
pub use Builtin::find_builtin;

// #[path = "type_check.rs"]
// pub mod TypeCheck;

#[path = "interpreter.rs"]
pub(crate) mod Interpreter;
// pub use Interpreter::State;

// genral imports
use anyhow::{anyhow, Result};
use nom_locate::LocatedSpan;
use std::collections::HashMap;
use std::sync::{Arc, Mutex};

// CONSTS
// TYPES

#[derive(Clone, Debug)]
pub struct State(Arc<Mutex<StateInsides>>);

#[derive(Clone, Debug)]
struct StateInsides {
  map: HashMap<String, Value>,
  up_scope: Option<State>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InputOrigin {
  File(Arc<String>),
  Repl(Arc<String>),
}

pub(crate) type Span<'a> = LocatedSpan<&'a str, InputOrigin>;
pub(crate) type IResult<'a, O> = nom::IResult<Span<'a>, O, MyError>;
// FUNCTIONS

/// Turns repl input onto a span
pub fn repl_to_span<'a>(input: &'a str) -> Span<'a> {
  Span::new_extra(input.clone(), InputOrigin::Repl(Arc::new(input.to_owned())))
}

/// Turn file into span
/// Todo: File currently lives forever, make it stop
pub fn file_to_span(file_name: &str) -> Result<Span<'static>> {
  use std::fs::read_to_string;
  let text = read_to_string(file_name.clone())?;
  let text: &'static str = Box::leak(Box::new(text));

  Ok(Span::new_extra(
    text,
    InputOrigin::File(Arc::new(file_name.to_owned())),
  ))
}
///// Open the file on computer and read its contents into a span.
//pub fn file_to_span<'a>(file: &mut std::fs::File, name: String) -> Result<Span<'a>> {
//  let mut text: String = String::from("");
//  file.read_to_string(&mut text)?;
//  return Ok(Span::new_extra(&text.clone, &name));
//}
///// Make a span from text and name it with name.
//pub fn text_to_span<'a>(text: &str, name: &str) -> Result<Span<'a>> {
//  todo!()
//}

/// converts an IRestult from nom to a normal anyhow Result
pub fn iresult_to_result<T>(x: IResult<T>) -> Result<T> {
  match x {
    std::result::Result::Ok((_s, out)) => Ok(out),
    Err(nom::Err::Error(e)) => return Err(anyhow!("{}", e.to_string())),
    Err(nom::Err::Incomplete(_)) => return Err(anyhow!("Parseing incomplete")),
    Err(nom::Err::Failure(e)) => return Err(anyhow!("{}", e.to_string())),
  }
}

/// Parse one span as an expr
pub fn parse_expr(input: &Span) -> Result<AST> {
  iresult_to_result(Parse::parse1(input.to_owned()))
}

/// Parse a slice of spans.
pub fn parse_spans(input: &[Span]) -> Result<Vec<AST>> {
  let mut ast = Vec::new();
  let mut i = 0;
  while let Some(file) = input.get(i) {
    i += 1;
    let parsed = Parse::parse(file.to_owned());
    match parsed {
      std::result::Result::Ok((_s, mut out)) => ast.append(&mut out),
      Err(nom::Err::Error(e)) => return Err(anyhow!("{}", e.to_string())),
      Err(nom::Err::Incomplete(_)) => return Err(anyhow!("Parseing incomplete")),
      Err(nom::Err::Failure(e)) => return Err(anyhow!("{}", e.to_string())),
    }
  }
  return Ok(ast);
}

// /// Type check a slice of Spans given a state.
// pub fn type_check_spans(input: &[Span], state: &mut State) -> Result<AST> {
//   let parsed = parse_spans(input)?;
//   let checked = TypeCheck::check_types(&parsed, &state)?;
//   return Ok(checked);
// }
//
// /// run a slice of inputs through the parser, concatenate them and then type check and run the code.
pub fn run(input: &[Span], state: &mut State) -> Result<Value> {
  let mut ret = Value::Int(0);
  let asts: Vec<AST> = parse_spans(input)?;
  for ast in asts {
    ret = Interpreter::interperate(&ast, state)?;
  }
  return Ok(ret);
}

pub fn run1(input: &Span, state: &mut State) -> Result<Value> {
  let parsed = parse_expr(input)?;
  Ok(Interpreter::interperate(&parsed, state)?)
}

// TRAITS
// IMPLS

impl InputOrigin {
  pub fn get_lines(&self) -> Result<Vec<String>> {
    use InputOrigin::*;

    use std::io::{BufRead, BufReader};
    match self {
      Repl(input) => Ok(input.split("\n").map(|x| x.to_string()).collect()),
      File(file_name) => {
        let file = std::fs::File::open(file_name.as_str())?;
        Ok(
          BufReader::new(file)
            .lines()
            .into_iter()
            .filter_map(|x| x.ok())
            .collect::<Vec<String>>(),
        )
      }
    }
  }
}

impl State {
  /// create an empty state
  pub fn empty() -> Self {
    Self::new(None)
  }
  /// create a new scope with a reference to an uper scope, if one exists.
  pub fn new(up_scope: Option<Self>) -> Self {
    State(Arc::new(Mutex::new(StateInsides::new(up_scope))))
  }
  /// create a new scope with |self| as the parent scope
  pub fn new_scope(&self) -> Self {
    Self::new(Some(self.clone()))
  }

  /// Declare a new variable in scope
  /// Errors if variable already exists
  pub fn declare(&mut self, var: String, val: Value) -> Result<()> {
    let State(ref mut insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().declare(var, val)
  }
  /// Assign a value to a variable that already exists
  /// Errors if variable does not exist
  pub fn assign(&mut self, var: String, val: Value) -> Result<()> {
    let State(ref mut insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().assign(var, val)
  }

  pub fn lookup(&self, var: String) -> Option<Value> {
    let State(ref insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().lookup(var)
  }
}

impl StateInsides {
  /// create a new scope with a reference to an uper scope, if one exists.
  pub fn new(up_scope: Option<State>) -> Self {
    Self {
      map: HashMap::new(),
      up_scope: up_scope,
    }
  }
  /// Declare a new variable in scope
  /// Errors if variable already exists
  pub fn declare(&mut self, var: String, val: Value) -> Result<()> {
    match self.map.get(&var) {
      Some(_) => Err(anyhow!(
        "Variable \"{var}\" already declared in current scope"
      )),
      None => {
        self.map.insert(var, val);
        Ok(())
      }
    }
  }
  /// Assign a value to a variable that already exists
  /// Errors if variable does not exist
  pub fn assign(&mut self, var: String, val: Value) -> Result<()> {
    match self.map.get(&var) {
      // If in current scope, assign
      Some(_) => {
        self.map.insert(var, val);
        Ok(())
      }
      // If not in current scope, assign in higher scope
      None => match &self.up_scope {
        Some(scope) => scope.clone().assign(var, val),
        None => Err(anyhow!("Could not find \"{var}\" in current scope")),
      },
    }
  }
  /// Find the value for a variable in scope
  pub fn lookup(&self, var: String) -> Option<Value> {
    match self.map.get(&var) {
      // return value in current scope
      Some(x) => Some(x.to_owned()),
      // return value in higher scope
      None => match &self.up_scope {
        Some(scope) => scope.lookup(var),
        None => None,
      },
    }
  }
}

unsafe impl Send for StateInsides {}
unsafe impl Send for State {}

// TESTS
