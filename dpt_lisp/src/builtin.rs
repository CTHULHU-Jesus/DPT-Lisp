// IMPORTS

use super::{
  ErrorKind,
  Interpreter::{interperate, to_myerror, RuntimeError},
  LBuiltinF, LFunction, MyError,
  Parse::LBuiltinM,
  State, TypeBinding, Value, AST,
};
use anyhow::{anyhow, Result};
use lazy_static::lazy_static;
use std::ops::Add;
use std::{collections::HashMap, str::FromStr};
// CONSTS
lazy_static! {
  static ref FUNCTION_MAP: HashMap<String, LBuiltinF> = {
    let mut m: HashMap<String, LBuiltinF> = HashMap::new();
    m.insert("list".to_owned(), list);
    m.insert("+".to_owned(), add);
    m.insert("-".to_owned(), subtract);
    m.insert("*".to_owned(), multiply);
    m.insert("/".to_owned(), divide);
    m.insert("println".to_owned(), l_println);
    m.insert("print".to_owned(), l_print);
    m.insert("xor".to_owned(), b_xor);
    m
  };
  static ref MACRO_MAP: HashMap<String, LBuiltinM> = {
    let mut m: HashMap<String, LBuiltinM> = HashMap::new();
    m.insert("print-ast".to_owned(), l_print_ast);
    m.insert("or".to_owned(), b_or);
    m.insert("and".to_owned(), b_and);
    m.insert("if".to_owned(), b_if);
    m
  };
  static ref TYPE_MAP: HashMap<String, TypeBinding> = {
    let mut m: HashMap<String, TypeBinding> = HashMap::new();
    m.insert(
      "+".to_owned(),
      TypeBinding::from_str("-> *Int Int").unwrap(),
    );
    m.insert(
      "-".to_owned(),
      TypeBinding::from_str("-> *Int Int").unwrap(),
    );
    m.insert(
      "*".to_owned(),
      TypeBinding::from_str("-> *Int Int").unwrap(),
    );
    m.insert(
      "/".to_owned(),
      TypeBinding::from_str("-> *Int Int").unwrap(),
    );
    m.insert(
      "println".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
    m.insert(
      "print".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
    m.insert(
      "xor".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );

    m.insert(
      "print-ast".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
    m.insert(
      "or".to_owned(),
      TypeBinding::from_str("-> *Bool Bool").unwrap(),
    );
    m.insert(
      "and".to_owned(),
      TypeBinding::from_str("-> *Bool Bool").unwrap(),
    );
    m.insert(
      "if".to_owned(),
      TypeBinding::from_str("-> Bool Any Any Any").unwrap(),
    );

    m
  };
}

// TYPES

// FUNCTIONS
/// Inital state with all of the builtins
pub fn inital_state() -> HashMap<String, Value> {
  let mut state = HashMap::new();
  for (name, f) in &*FUNCTION_MAP {
    state.insert(
      name.clone(),
      Value::Fun(LFunction::BuiltinF(name.clone(), *f), State::empty()),
    );
  }
  for (name, f) in &*MACRO_MAP {
    state.insert(
      name.clone(),
      Value::Fun(LFunction::BuiltinM(name.clone(), *f), State::empty()),
    );
  }
  state
}
/// Inital context with all of the builtins and there types
pub fn inital_context() -> HashMap<String, TypeBinding> {
  return (*TYPE_MAP).clone();
}

pub fn find_builtin(name: String) -> Option<LFunction> {
  let mut name = name.clone();
  match (*FUNCTION_MAP).get(&mut name) {
    Some(fun) => Some(LFunction::BuiltinF(name.clone(), *fun)),
    None => Some(LFunction::BuiltinM(
      name.clone(),
      *(*MACRO_MAP).get(&mut name)?,
    )),
  }
}

fn l_println(l: &mut Vec<Value>) -> Result<Value> {
  for a in l {
    println!("{a}");
  }
  return Ok(Value::List(vec![]));
}

fn l_print(l: &mut Vec<Value>) -> Result<Value> {
  for a in l {
    print!("{a}");
  }
  print!("\n");
  return Ok(Value::List(vec![]));
}

fn l_print_ast(_state: &mut State, l: &mut Vec<AST>) -> Result<Value, MyError> {
  for a in l {
    println!("{a}");
  }
  return Ok(Value::List(vec![]));
}

/// Function to create list
fn list(l: &mut Vec<Value>) -> Result<Value> {
  Ok(Value::List(l.to_vec()))
}

fn b_if(state: &mut State, l: &mut Vec<AST>) -> Result<Value, MyError> {
  if l.len() != 3 {
    return Err(MyError::unknown_error());
  }
  let cond = &l[0];
  let then = &l[1];
  let else_ = &l[2];
  // evaluate condition
  let cond: bool = to_myerror(interperate(&cond, state)?.to_bool(), &cond.position())?;
  // eval then or else
  if cond {
    interperate(&then, state)
  } else {
    interperate(&else_, state)
  }
}

/// shortsirket and
fn b_and(state: &mut State, l: &mut Vec<AST>) -> Result<Value, MyError> {
  if l.len() == 0 {
    return Ok(Value::Bool(true));
  }
  let mut b: bool = true;
  let mut n = 0;
  while b != false {
    match l.get(n) {
      Some(ast) => {
        let val = interperate(&ast, state)?;
        b = b && to_myerror(val.to_bool(), &ast.position())?;
      }
      None => break,
    }

    n += 1;
  }
  return Ok(Value::Bool(b));
}

/// shortsirket or
fn b_or(state: &mut State, l: &mut Vec<AST>) -> Result<Value, MyError> {
  if l.len() == 0 {
    return Ok(Value::Bool(true));
  }
  let mut b: bool = false;
  let mut n = 0;
  while b != true {
    match l.get(n) {
      Some(ast) => {
        let val = interperate(&ast, state)?;
        b = b || to_myerror(val.to_bool(), &ast.position())?;
      }
      None => break,
    }

    n += 1;
  }
  return Ok(Value::Bool(b));
}

/// xor bools
fn b_xor(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() == 0 {
    return Ok(Value::Bool(true));
  }
  let mut b = l[0].to_bool()?;
  for val in l[1..].to_owned() {
    b = b ^ val.to_bool()?;
  }
  return Ok(Value::Bool(b));
}

/// divide numbers
fn divide(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() == 0 {
    return Ok(Value::Int(1));
  }
  let mut s: i128 = l[0].to_int()?;
  for val in l[1..].to_owned() {
    s /= val.to_int()?;
  }
  return Ok(Value::Int(s));
}

/// multiply numbers
fn multiply(l: &mut Vec<Value>) -> Result<Value> {
  let mut s: i128 = 1;
  for val in l {
    s *= val.to_int()?;
  }
  return Ok(Value::Int(s));
}

/// Subtract numbers
fn subtract(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() == 0 {
    return Ok(Value::Int(0));
  }
  let mut s: i128 = l[0].to_int()?;
  for val in l[1..].to_owned() {
    s -= val.to_int()?;
  }
  return Ok(Value::Int(s));
}

/// Add numbers
fn add(l: &mut Vec<Value>) -> Result<Value> {
  let mut s: i128 = 0;
  for val in l {
    s += val.to_int()?;
  }
  return Ok(Value::Int(s));
}

// TRAITS
// IMPLS
// TESTS
