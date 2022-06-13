// IMPORTS

use super::{
  find_builtin, ErrorKind, FileLocation, IResult, InputOrigin, Interpreter, MyError, Span, State,
};
use anyhow::{anyhow, Result};
use lazy_static::lazy_static;
use nom::{
  branch::alt,
  bytes::complete::tag,
  character::complete::*,
  combinator::{cut, map, opt},
  multi::{many0, many1},
  InputIter,
};
use nom_locate::position;
use std::{fmt::Display, i128, string, sync::Arc};

// CONSTS
/// List of characters that count as whitespace. Stolen from https://doc.rust-lang.org/reference/whitespace.html
const WHITESPACE: &str =
  "\u{0009}\u{000A}\u{000B}\u{000C}\u{000D}\u{0020}\u{0085}\u{200E}\u{200F}\u{2028}\u{2029}";
lazy_static! {
    static ref __RESTRICTED_CHARS: String = vec!["()'#[]\".", WHITESPACE].join("");
    /// List of characters that cant be used in variable names
    static ref RESTRICTED_CHARS: &'static str = __RESTRICTED_CHARS.as_str();
}
// TYPES

#[derive(Clone, Debug)]
/// Abstract syntax tree for language
pub enum AST {
  /// Node to hold functions (bultins and lambdas)
  Fun(LFunction, FileLocation),
  /// Node to hold let expressions
  Let(Vec<(String, AST)>, Box<AST>, FileLocation),
  /// Node to hold a s-expression
  Sexpr(Vec<AST>, FileLocation),
  /// Node to hold a variable
  Var(String, FileLocation),
  /// Node to hold a value that needs no more evaluation
  Val(Value, FileLocation),
  /// Add a variable (with value ) to current scope
  Define(String, Box<AST>, FileLocation),
  /// Set pre defined variable with a value
  Set(String, Box<AST>, FileLocation),
}

/// LBuiltinF (Lisp builtin) is the function pointer type
pub type LBuiltinF = fn(&mut Vec<Value>) -> Result<Value>;

/// LBuiltinM (Lisp builtin) is the function pointer type that
/// can act as a macro
pub type LBuiltinM = fn(&mut State, &mut Vec<AST>) -> Result<Value, MyError>;

/// There are two types of function - builtin and lambda
#[derive(Clone)]
pub enum LFunction {
  /// (name, function pointer)
  BuiltinF(String, LBuiltinF),
  /// (name, function pointer)
  BuiltinM(String, LBuiltinM),
  /// lambda function (args, body), args are a list of variable names (types comeing soon //TODO)
  LambdaF(Vec<String>, Box<AST>),
  /// lambda macro (args, body), args are a list of variable names (types comeing soon //TODO)
  LambdaM(Vec<String>, Box<AST>),
}

#[derive(Clone, Debug)]
pub enum Value {
  /// A char value
  Char(char),
  /// Clasic Pair value (cons, car, cdr operations)
  Pair(Box<Value>, Box<Value>),
  /// An int
  Int(i128),
  /// A string "xxx"
  Str(String),
  /// A list of values
  List(Vec<Value>),
  /// A function with a pointer to state
  Fun(LFunction, State),
  /// A boolean, true(#t) or false(#f)
  Bool(bool),
  /// A wraper for AST to eval,
  /// passed to macros
  Meval(Box<AST>, State),
}

// FUNCTIONS

/// Parse one expression
pub fn parse1(s: Span) -> IResult<AST> {
  let (s, expr) = all_expr(s)?;
  let (s, _) = whitespace(s)?;
  if s.is_empty() {
    return IResult::Ok((s, expr));
  } else {
    let pos = match position(s) {
      IResult::Ok((_, x)) => x,
      _ => Span::new_extra(
        "Unknown error. unable to find span",
        InputOrigin::Repl(Arc::new("unknown".to_owned())),
      ),
    };
    return IResult::Err(nom::Err::Failure(MyError::new_from_span(
      ErrorKind::Parse,
      pos,
      None,
    )));
  }
}
/// Parse an entire file
pub fn parse(s: Span) -> IResult<Vec<AST>> {
  let (s, exprs) = many0(all_expr)(s)?;
  // Filter out the Nones
  let (s, _) = whitespace(s)?;
  if s.is_empty() {
    return IResult::Ok((s, exprs));
  } else {
    println!("not empty");
    let pos = match position(s) {
      IResult::Ok((_, x)) => x,
      _ => Span::new_extra(
        "Unknown error. unable to find span",
        InputOrigin::Repl(Arc::new("unknown".to_owned())),
      ),
    };
    return IResult::Err(nom::Err::Failure(MyError::new_from_span(
      ErrorKind::Parse,
      pos,
      None,
    )));
  }
}

/// parse whitespace
fn whitespace(s: Span) -> IResult<()> {
  fn one_whitespace(s: Span) -> IResult<()> {
    let (s, _) = one_of(WHITESPACE)(s)?;
    return IResult::Ok((s, ()));
  }
  let (s, _) = many0(alt((comment, one_whitespace)))(s)?;
  return IResult::Ok((s, ()));
}

/// Parse a char in a string (allows escape sequences)
/// TODO{allow escape sequences}
fn generic_char(s: Span) -> IResult<char> {
  none_of("\"")(s)
}

/// Parse one expression and consume comments
fn all_expr(s: Span) -> IResult<AST> {
  // find comment
  let (s, _) = whitespace(s)?;
  let (s, _) = opt(comment)(s)?;
  let (s, _) = whitespace(s)?;
  let (s, e) = alt((lambda, define, set, let_expr, expr, value, variable))(s)?;
  let (s, _) = whitespace(s)?;
  return IResult::Ok((s, e));
}

/// Parse annonamas functions
fn lambda(s: Span) -> IResult<AST> {
  fn var(s: Span) -> IResult<String> {
    let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
    let (s, _) = whitespace(s)?;
    let var: String = var.into_iter().collect();
    return IResult::Ok((s, var));
  }
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  // macro or function
  let (s, kind) = alt((tag("mlambda"), tag("mλ"), tag("λ"), tag("lambda")))(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char('(')(s)?;
  let (s, args) = many0(var)(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char(')')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, body) = all_expr(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  // If function
  if vec!["λ", "lambda"].contains(&kind) {
    return IResult::Ok((
      s,
      AST::Fun(LFunction::LambdaF(args, Box::new(body)), location),
    ));
  } else {
    // If macro
    return IResult::Ok((
      s,
      AST::Fun(LFunction::LambdaM(args, Box::new(body)), location),
    ));
  }
}

/// Parse a define expression
fn define(s: Span) -> IResult<AST> {
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = tag("define")(s)?;
  let (s, _) = whitespace(s)?;
  let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
  let (s, _) = whitespace(s)?;
  let (s, body) = all_expr(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  let var: String = var.into_iter().collect();
  return IResult::Ok((s, AST::Define(var, Box::new(body), location)));
}

/// Parse a set expression
fn set(s: Span) -> IResult<AST> {
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = tag("set")(s)?;
  let (s, _) = whitespace(s)?;
  let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
  let (s, _) = whitespace(s)?;
  let (s, body) = all_expr(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  let var: String = var.into_iter().collect();
  return IResult::Ok((s, AST::Set(var, Box::new(body), location)));
}

/// Parse a let-expression
fn let_expr(s: Span) -> IResult<AST> {
  fn binding(s: Span) -> IResult<(String, AST)> {
    let (s, _) = char('(')(s)?;
    let (s, _) = whitespace(s)?;
    let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
    let (s, _) = whitespace(s)?;
    let (s, body) = all_expr(s)?;
    let (s, _) = whitespace(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = whitespace(s)?;
    let var: String = var.into_iter().collect();
    return IResult::Ok((s, (var, body)));
  }
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = tag("let")(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char('(')(s)?;
  let (s, bindings) = many0(binding)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, body) = all_expr(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  return IResult::Ok((s, AST::Let(bindings, Box::new(body), location)));
}

/// Parse an s-expression
fn expr(s: Span) -> IResult<AST> {
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, args) = many1(all_expr)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  return IResult::Ok((s, AST::Sexpr(args, location)));
}

// /// Parse variables
// fn variable(s: Span) -> IResult<AST> {
//   let (s, pos1) = position(s)?;
//   let (s, var) = many1(none_of(WHITESPACE))(s)?;
//   let (s, pos2) = position(s)?;
//   let location = FileLocation::new(pos1, Some(pos2));
//   return IResult::Ok((s, AST::Var(var.iter().collect(), location)));
// }

/// Parse a variable or a builtin
fn variable(s: Span) -> IResult<AST> {
  let (s, pos1) = position(s)?;
  let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
  let (s, pos2) = position(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  let var: String = var.iter().collect();
  let node = match find_builtin(var.clone()) {
    Some(f) => AST::Fun(f, location),
    None => AST::Var(var, location),
  };

  return IResult::Ok((s, node));
}

/// Parse an atomic value
fn value(s: Span) -> IResult<AST> {
  /// signed 128 bit variable
  fn integer(s: Span) -> IResult<Value> {
    let (s, i) = i128(s)?;
    IResult::Ok((s, Value::Int(i)))
  }
  /// boolean #t or #f
  fn boolean(s: Span) -> IResult<Value> {
    let (s, b) = alt((tag("#t"), tag("#f")))(s)?;
    let b: String = b.to_string();
    let b = if b == "#t" { true } else { false };
    IResult::Ok((s, Value::Bool(b)))
  }

  /// character #'c
  fn charector(s: Span) -> IResult<Value> {
    let (s, _) = tag("#'")(s)?;
    let (s, c) = generic_char(s)?;
    IResult::Ok((s, Value::Char(c)))
  }
  fn my_string(s: Span) -> IResult<Value> {
    let (s, _) = tag("\"")(s)?;
    let (s, string) = many0(generic_char)(s)?;
    let (s, _) = tag("\"")(s)?;
    let string: String = string.iter().collect();
    IResult::Ok((s, Value::Str(string)))
  }
  // TODO Symbol
  // fn symbol(s: Span) -> IResult<Value> {
  //   let (s, _) = tag("'")(s)?;
  //   let (s, sym) = many1(none_of("\t\r\n "))(s)?;
  //   let sym: String = sym.iter().collect();
  //   IResult::Ok((s, Value::Sym(sym)))
  // }
  let (s, pos1) = position(s)?;
  let (s, value) = alt((boolean, integer, charector, my_string))(s)?;
  let (s, pos2) = position(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  return IResult::Ok((s, AST::Val(value, location)));
}

fn comment(s: Span) -> IResult<()> {
  let (s, _) = tag(";;")(s)?;
  let (s, _) = many0(none_of("\r\n"))(s)?;
  if s.is_empty() {
    return IResult::Ok((s, ()));
  } else {
    let (s, _) = newline(s)?;
    return IResult::Ok((s, ()));
  }
}

// TRAITS
// IMPLS

impl Value {
  /// If the value is an Meval (a placeholder) evaluate it to its final value.
  pub fn eval_if_needed(&self) -> Result<Value, MyError> {
    match self {
      Value::Meval(ast, state) => Interpreter::interperate(&ast, &mut state.clone()),
      _ => Ok(self.to_owned()),
    }
  }

  pub fn to_int(&self) -> Result<i128> {
    match self {
      Value::Int(i) => Ok(*i),
      _ => Err(anyhow!("expected int")),
    }
  }

  pub fn to_bool(&self) -> Result<bool> {
    match self {
      Value::Bool(i) => Ok(*i),
      _ => Err(anyhow!("expected bool")),
    }
  }

  pub fn to_fun(&self) -> Result<(&LFunction, State)> {
    match self {
      Value::Fun(fun, state) => Ok((fun, state.clone())),
      _ => Err(anyhow!("expected function")),
    }
  }

  pub fn to_char(&self) -> Result<char> {
    match self {
      Value::Char(c) => Ok(*c),
      _ => Err(anyhow!("expected char")),
    }
  }

  pub fn to_str(&self) -> Result<String> {
    match self {
      Value::Str(s) => Ok(s.clone()),
      _ => Err(anyhow!("expected char")),
    }
  }
  pub fn to_list(&self) -> Result<Vec<Value>> {
    match self {
      Value::List(xs) => Ok(xs.clone()),
      _ => Err(anyhow!("expected char")),
    }
  }
}
impl Display for LFunction {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use LFunction::*;
    match &self {
      BuiltinF(name, _) => write!(f, "{}", name),
      BuiltinM(name, _) => write!(f, "{}", name),
      LambdaF(args, body) => write!(f, "(λ ({args:?}), {body})"),
      LambdaM(args, body) => write!(f, "(mλ ({args:?}), {body})"),
    }
  }
}

impl std::fmt::Debug for LFunction {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use LFunction::*;
    match &self {
      BuiltinF(name, _) => write!(f, "LFunction::BultinF({name:?},function_pointer)"),
      BuiltinM(name, _) => write!(f, "LFunction::BultinM({name:?},function_pointer)"),
      LambdaF(args, body) => write!(f, "LFunction::LambdaF({args:?},{body:?})"),
      LambdaM(args, body) => write!(f, "LFunction::LambdaM({args:?},{body:?})"),
    }
  }
}

impl Display for Value {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use Value::*;
    match self {
      Pair(car, cdr) => write!(f, "(cons {car} {cdr})"),
      Fun(fun, _state) => write!(f, "{fun}"),
      Char(c) => write!(f, "#'{c}"),
      Meval(body, _state) => write!(f, "`{body}`"),
      Bool(b) => {
        if *b {
          write!(f, "#t")
        } else {
          write!(f, "#f")
        }
      }
      Int(i) => write!(f, "{i}"),
      Str(s) => write!(f, "\"{s}\""),
      List(xs) => {
        write!(f, "(list")?;
        for x in xs {
          write!(f, " {x}")?;
        }
        write!(f, ")")
      }
    }
  }
}

impl Display for AST {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      AST::Var(a, _) => write!(f, "{a}"),
      AST::Val(a, _) => write!(f, "{a}"),
      AST::Fun(fun, _) => write!(f, "{fun}"),
      AST::Define(var, def, _) => write!(f, "(define {var} {def})"),
      AST::Set(var, def, _) => write!(f, "(set {var} {def})"),
      AST::Let(bindings, body, _) => {
        write!(f, "(let (")?;
        for (var, val) in bindings {
          write!(f, "({var} {val})")?;
        }
        write!(f, ") {body})")
      }
      AST::Sexpr(xs, _) => {
        write!(f, "(")?;
        for x in xs {
          write!(f, " {x}")?;
        }
        write!(f, ")")
      }
    }
  }
}

impl AST {
  pub fn position(&self) -> FileLocation {
    use AST::*;
    match self {
      Set(_, _, l) => l.clone(),
      Define(_, _, l) => l.clone(),
      Var(_, l) => l.clone(),
      Fun(_, l) => l.clone(),
      Let(_, _, l) => l.clone(),
      Val(_, l) => l.clone(),
      Sexpr(_, l) => l.clone(),
    }
  }

  pub fn as_text(&self) -> String {
    format!("{}", self)
  }
}
// TESTS
