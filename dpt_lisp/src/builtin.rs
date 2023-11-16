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
      // List ops
    m.insert("list".to_owned(), list);
    m.insert("insert".to_owned(), l_insert);
    m.insert("nth".to_owned(), l_nth);
    m.insert("empty?".to_owned(), l_empty);
    m.insert("length".to_owned(), l_length);
      // Pair ops
    m.insert("car".to_owned(), car);
    m.insert("cdr".to_owned(), cdr);
    m.insert("cons".to_owned(), cons);
      // Math ops
    m.insert("zero?".to_owned(), is_zero);
    m.insert("+".to_owned(), add);
    m.insert("-".to_owned(), subtract);
    m.insert("*".to_owned(), multiply);
    m.insert("/".to_owned(), divide);
      // Print ops
    m.insert("println".to_owned(), l_println);
    m.insert("print".to_owned(), l_print);
      // Boolean ops
    m.insert("xor".to_owned(), b_xor);
    m.insert("eq?".to_owned(), is_equal);
    m.insert("assert".to_owned(), assert_true);
    m
  };
  static ref MACRO_MAP: HashMap<String, LBuiltinM> = {
    let mut m: HashMap<String, LBuiltinM> = HashMap::new();
      // print ops
    m.insert("print-ast".to_owned(), l_print_ast);
      // boolean ops
    m.insert("or".to_owned(), b_or);
    m.insert("and".to_owned(), b_and);
    m.insert("if".to_owned(), b_if);
    m
  };

  /// Map of deffinitons for types
  /// Empty for now
  static ref TYPE_DEFFIN_MAP: HashMap<String, TypeBinding> = {
    let mut m: HashMap<String, TypeBinding> = HashMap::new();
    m
  };
  /// Map of type deffinitons for functions
  static ref TYPE_MAP: HashMap<String, TypeBinding> = {
    let mut m: HashMap<String, TypeBinding> = HashMap::new();
      // list ops
    m.insert("list".to_owned(), TypeBinding::from_str("-> *x (List x)").unwrap());
    m.insert("insert".to_owned(), TypeBinding::from_str("-> (List x) x Int (List x)").unwrap());
    m.insert("nth".to_owned(), TypeBinding::from_str("-> (List x) Int x").unwrap());
    m.insert("empty?".to_owned(), TypeBinding::from_str("-> (List x) Bool").unwrap());
    m.insert("length".to_owned(), TypeBinding::from_str("-> (List x) Int").unwrap());
      // Pair ops
    m.insert(
      "car".to_owned(),
      TypeBinding::from_str("-> (Pair x y) x").unwrap(),
    );
    m.insert(
      "cdr".to_owned(),
      TypeBinding::from_str("-> (Pair x y) y").unwrap(),
    );
    m.insert(
      "cons".to_owned(),
      TypeBinding::from_str("-> x y (Pair x y)").unwrap()
    );
      // Math ops
    m.insert(
      "zero?".to_owned(),
      TypeBinding::from_str("-> Int Bool").unwrap(),
    );
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
      // print ops
    m.insert(
      "println".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
    m.insert(
      "print-ast".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
    m.insert(
      "print".to_owned(),
      TypeBinding::from_str("-> *Any Unit").unwrap(),
    );
      // boolean ops
    m.insert(
      "xor".to_owned(),
      TypeBinding::from_str("-> *Bool Unit").unwrap(),
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
      TypeBinding::from_str("-> Bool x x x").unwrap(),
    );
    m.insert(
      "eq?".to_owned(),
      TypeBinding::from_str("-> x x Bool").unwrap(),
    );
    m.insert(
      "assert".to_owned(),
      TypeBinding::from_str("-> *Bool Unit").unwrap(),
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
/// and type deffinitons
/// reutrns (types of variables, deffinitons of types)
pub fn inital_context() -> (HashMap<String, TypeBinding>, HashMap<String, TypeBinding>) {
  return ((*TYPE_MAP).clone(), (*TYPE_DEFFIN_MAP).clone());
}

// pub fn find_builtin(name: String) -> Option<LFunction> {
//   let mut name = name.clone();
//   match (*FUNCTION_MAP).get(&mut name) {
//     Some(fun) => Some(LFunction::BuiltinF(name.clone(), *fun)),
//     None => Some(LFunction::BuiltinM(
//       name.clone(),
//       *(*MACRO_MAP).get(&mut name)?,
//     )),
//   }
// }

// Lisp Ops
/// Function to create list
fn list(l: &mut Vec<Value>) -> Result<Value> {
  Ok(Value::List(l.to_vec()))
}
/// insert a value into a list
fn l_insert(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 3 {
    return Err(anyhow!("wrong number of arguments"));
  }
  let mut lst = l[0].to_list()?.clone();
  let elem = l[1].clone();
  let n = l[2].to_int()?;
  if (n as usize) < lst.len() {
    lst.insert(n as usize, elem);
    Ok(Value::List(lst))
  } else {
    Err(anyhow!("{n} is out of bounds for list {lst:?}."))
  }
}
/// Get the nth value in a list, can error if n is not in bounds
fn l_nth(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 2 {
    return Err(anyhow!("wrong number of arguments"));
  }
  let lst = l[0].to_list()?;
  let n = l[1].to_int()?;
  lst
    .get(n as usize)
    .map(|x| x.clone())
    .ok_or(anyhow!("{n} is out of bounds for list {lst:?}."))
}

/// returns true if a list is empty
fn l_empty(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 1 {
    return Err(anyhow!("wrong number of arguments"));
  }
  match &l[0] {
    Value::List(x) => Ok(Value::Bool(x.is_empty())),
    _ => Err(anyhow!("wrong argument type")),
  }
}
/// returns the length of a list
fn l_length(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 1 {
    return Err(anyhow!("wrong number of arguments"));
  }
  match &l[0] {
    Value::List(x) => Ok(Value::Int(x.len() as i128)),
    _ => Err(anyhow!("wrong argument type")),
  }
}
// Pair Ops
/// Pair operation, gets first value in pair.
fn car(l: &mut Vec<Value>) -> Result<Value> {
  // get pair
  let p = l.get(0).ok_or(anyhow!("No argument given"))?;
  match p {
    Value::Pair(a, _) => Ok(*a.clone()),
    _ => Err(anyhow!("argument must be of type pair")),
  }
}
/// Pair operation, gets second value in pair.
fn cdr(l: &mut Vec<Value>) -> Result<Value> {
  // get pair
  let p = l.get(0).ok_or(anyhow!("No argument given"))?;
  match p {
    Value::Pair(_, b) => Ok(*b.clone()),
    _ => Err(anyhow!("argument must be of type pair")),
  }
}
/// Pair operation, constructs a pair
fn cons(l: &mut Vec<Value>) -> Result<Value> {
  // get args
  if l.len() != 2 {
    return Err(anyhow!("not enough arguments"));
  }
  Ok(Value::Pair(Box::new(l[0].clone()), Box::new(l[1].clone())))
}
// Math Ops
/// test if number is zero
fn is_zero(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 1 {
    return Err(anyhow!("wrong number of arguments"));
  }
  Ok(Value::Bool(l[0].to_int()? == 0))
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
// Print Ops
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
// Boolean Ops

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

/// test that 2 values are equal
fn is_equal(l: &mut Vec<Value>) -> Result<Value> {
  if l.len() != 2 {
    return Err(anyhow!("wrong number of arguments"));
  }
  let a : &Value = &l[0];
  let b : &Value = &l[1];
  Ok(Value::Bool(a == b))
}
/// crashes if all values are not true
fn assert_true(l: &mut Vec<Value>) -> Result<Value> {
  let b: bool = l
    .iter()
    .map(|x| x.to_bool())
    .collect::<Result<Vec<bool>>>()?
    .iter()
    .fold(true, |a, b| a && *b);
  if b {
    Ok(Value::Unit)
  } else {
    Err(anyhow!("assertion failed"))
  }
}

// TRAITS
// IMPLS
// TESTS
mod test_builtin {
  use super::{FUNCTION_MAP, MACRO_MAP, TYPE_MAP};

  /// Makes shure all functions in FUNCTION_MAP and MACRO_MAP
  /// have types in TYPE_MAP.
  #[test]
  fn all_builtins_have_types() {
    for (k, _) in FUNCTION_MAP.clone().into_iter() {
      assert!(TYPE_MAP.get(&k).is_some());
    }
    for (k, _) in MACRO_MAP.clone().into_iter() {
      assert!(TYPE_MAP.get(&k).is_some());
    }
  }
  /// Make shure that everything in TYPE_MAP has a
  /// corrosponding implimentation in FUNCTION_MAP
  /// or MACRO_MAP
  #[test]
  fn all_types_have_builtins() {
    for (k, _) in TYPE_MAP.clone().into_iter() {
      assert!(FUNCTION_MAP.get(&k).is_some() || MACRO_MAP.get(&k).is_some())
    }
  }
}
