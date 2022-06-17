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

#[path = "type_check.rs"]
pub mod TypeCheck;

#[path = "interpreter.rs"]
pub(crate) mod Interpreter;
// pub use Interpreter::State;

// genral imports
use anyhow::{anyhow, Result};
use nom_locate::LocatedSpan;
use std::collections::HashMap;
use std::fmt::Display;
use std::str::FromStr;
use std::sync::{Arc, Mutex};

// CONSTS
// TYPES

pub type Binding = (String, Option<TypeBinding>, Box<AST>);
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TypeBinding {
  /// Type representing an arbitrary number of arguments of some type
  Star(Box<TypeBinding>),
  /// Any type (use wisely)
  Any,
  /// Integer type
  Int,
  /// Boolean type (true,false)
  Bool,
  /// Function/Macro type (args types,return type)
  Arrow(Vec<TypeBinding>, Box<TypeBinding>),
  /// Charector type
  Char,
  /// The string type ("xxx")
  Str,
  /// type of Unit
  Unit,
  // TODO
  // TypeVar(String)
  // Pair(Box<TypeBinding>, Box<TypeBinding>),
  // List(Box<TypeBinding>)
}

#[derive(Clone, Debug)]
pub struct Context(Arc<Mutex<ContextInsides>>);

#[derive(Clone, Debug)]
struct ContextInsides {
  type_map: HashMap<String, TypeBinding>,
  up_scope: Option<Context>,
}

#[derive(Clone, Debug)]
pub struct State(Arc<Mutex<StateInsides>>);

#[derive(Clone, Debug)]
struct StateInsides {
  map: HashMap<String, Value>,
  // TODO: (needed for dependent types) type_map: HashMap<String, TypeBinding>,
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

// /// Turn file into span
// /// Todo: File currently lives forever, make it stop
// pub fn file_to_span(file_name: &str) -> Result<Span<'static>> {
//   use std::fs::read_to_string;
//   let text = read_to_string(file_name.clone())?;
//   let text: &'static str = Box::leak(Box::new(text));
//
//   Ok(Span::new_extra(
//     text,
//     InputOrigin::File(Arc::new(file_name.to_owned())),
//   ))
// }
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

/// Parse a slice of files
pub fn parse_files(input: &[String]) -> Result<Vec<AST>> {
  use std::fs::read_to_string;
  let mut ast = Vec::new();
  for file in input {
    // Open file and parse it
    let text = read_to_string(file.clone())?;
    let span = Span::new_extra(&text, InputOrigin::File(Arc::new(file.to_string())));

    let parsed = Parse::parse(span);
    match parsed {
      std::result::Result::Ok((_s, mut out)) => ast.append(&mut out),
      Err(nom::Err::Error(e)) => return Err(anyhow!("{}", e.to_string())),
      Err(nom::Err::Incomplete(_)) => return Err(anyhow!("Parseing incomplete")),
      Err(nom::Err::Failure(e)) => return Err(anyhow!("{}", e.to_string())),
    }
  }
  return Ok(ast);
}

/// Type check a list of files
pub fn type_check_files(input: &[String], context: &mut Context) -> Result<()> {
  let asts = parse_files(input)?;
  for mut ast in asts {
    TypeCheck::type_check(&mut ast, context)?;
  }
  return Ok(());
}

/// Type check one expression
pub fn type_check1(input: &Span, context: &mut Context) -> Result<()> {
  todo!()
}

/// run a slice of inputs through the parser, concatenate them and then type check and run the code.
pub fn run(input: &[String], state: &mut State) -> Result<Value> {
  let mut ret = Value::Int(0);
  let asts: Vec<AST> = parse_files(input)?;
  // @TODO: type check asts
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

impl Context {
  /// create a new scope with a reference to an uper scope, if one exists.
  fn new(up_scope: Option<Self>) -> Self {
    Context(Arc::new(Mutex::new(ContextInsides::new(up_scope))))
  }
  /// create a new scope with |self| as the parent scope
  pub fn new_scope(&self) -> Self {
    Self::new(Some(self.clone()))
  }

  /// Declare a new variable in scope
  /// Errors if variable already exists
  pub fn declare(&mut self, var: String, typ: TypeBinding) -> Result<()> {
    let Context(ref mut insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().declare(var, typ)
  }

  /// Look up the type of a variable
  pub fn lookup(&self, var: String) -> Option<TypeBinding> {
    let Context(ref insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().lookup(var)
  }
}

impl Default for Context {
  fn default() -> Self {
    Context(Arc::new(Mutex::new(ContextInsides::default())))
  }
}

impl ContextInsides {
  /// create a new scope with a reference to an uper scope, if one exists.
  pub fn new(up_scope: Option<Context>) -> Self {
    Self {
      type_map: HashMap::new(),
      up_scope: up_scope,
    }
  }
  /// Declare a new variable in scope
  /// Errors if variable already exists
  pub fn declare(&mut self, var: String, typ: TypeBinding) -> Result<()> {
    match self.type_map.get(&var) {
      Some(_) => Err(anyhow!(
					"Variable \"{var}\" already declared in current scope, if you want to change the value in \"{var}\" use set."
      )),
      None => {
        self.type_map.insert(var, typ);
        Ok(())
      }
    }
  }

  /// Find the type for a variable in scope
  pub fn lookup(&self, var: String) -> Option<TypeBinding> {
    match self.type_map.get(&var) {
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

impl Default for ContextInsides {
  fn default() -> Self {
    Self {
      type_map: Builtin::inital_context(),
      up_scope: None,
    }
  }
}

impl State {
  /// An empty state with nothing in it
  pub fn empty() -> Self {
    State(Arc::new(Mutex::new(StateInsides::new(None))))
  }
  /// create a new scope with a reference to an uper scope, if one exists.
  fn new(up_scope: Option<Self>) -> Self {
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

impl Default for State {
  fn default() -> Self {
    State(Arc::new(Mutex::new(StateInsides::default())))
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
impl Default for StateInsides {
  fn default() -> Self {
    StateInsides {
      map: Builtin::inital_state(),
      up_scope: None,
    }
  }
}

impl TypeBinding {
  /// Returns true if the type is a star type (e.x. *Int)
  pub fn is_star(&self) -> bool {
    match self {
      TypeBinding::Star(_) => true,
      _ => false,
    }
  }

  /// Returns true if one type can be coerced to the other
  /// When used in an assignment use this funtion like this:
  /// user_defined_type.same_as(other_type)
  pub fn same_as(&self, other: Self, context: &Context) -> bool {
    const any: TypeBinding = TypeBinding::Any;

    if self == &any || self == &other {
      true
    } else {
      match self {
        TypeBinding::Arrow(a_args, a_ret) => match other {
          TypeBinding::Arrow(b_args, b_ret) => {
            if a_args.len() != b_args.len() {
              false
            } else {
              let mut acc = true;
              for (a_arg, b_arg) in a_args.into_iter().zip(b_args.into_iter()) {
                acc = acc && a_arg.same_as(b_arg, context);
              }
              acc && a_ret.same_as(*b_ret, context)
            }
          }
          _ => false,
        },
        _ => false,
      }
    }
  }
}

impl Display for TypeBinding {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use TypeBinding::*;
    match self {
      Any => write!(f, "Any"),
      Int => write!(f, "Int"),
      Bool => write!(f, "Bool"),
      Char => write!(f, "Char"),
      Str => write!(f, "Str"),
      Unit => write!(f, "Unit"),
      Star(body) => write!(f, "*{body}"),
      Arrow(body, ret) => {
        write!(f, "(-> ")?;
        for arg in body {
          write!(f, "{arg} ")?;
        }
        write!(f, "{ret})")
      }
    }
  }
}

impl FromStr for TypeBinding {
  type Err = anyhow::Error;

  /// Parse a type
  fn from_str(s: &str) -> Result<Self, Self::Err> {
    // wrap the type with the requierd brackets
    let wraped = format!("[{s}]");

    let span = Span::new_extra(&wraped, InputOrigin::Repl(Arc::new(wraped.clone())));

    iresult_to_result(Parse::type_binding(span))
  }
}

unsafe impl Send for ContextInsides {}
unsafe impl Send for Context {}

unsafe impl Send for StateInsides {}
unsafe impl Send for State {}

// TESTS

/// Test the TypeBinding methods and implimentation
#[cfg(test)]
mod test_types {
  use super::*;

  /// Test the same_as method.
  /// Notes:
  /// 1. All types can bind to any, but any can't bind to any type but any.
  ///    (e.x. Any.same_as(Bool) good, Bool.same_as(Any) bad)
  #[test]
  fn same_as() {
    // TODO
  }

  /// Test the FromStr parseing
  /// Notes:
  /// 1. You should not be able to "Star" more than once (e.x. "*Int" works, "**Int" does not).
  /// 2. Star types should only come at the end of functions (e.x. "-> Int *Int Int" good, "-> *Int Int Int" bad)
  #[test]
  fn parseing() {
    // Test Any
    let any_p = TypeBinding::from_str("Any");
    let any = TypeBinding::Any;
    assert!(any_p.is_ok());
    assert_eq!(any_p.unwrap(), any);

    // Test Int
    let int_p = TypeBinding::from_str("Int");
    let int = TypeBinding::Int;
    assert!(int_p.is_ok());
    assert_eq!(int_p.unwrap(), int);

    // Test Bool
    let boolean_p = TypeBinding::from_str("Bool");
    let boolean = TypeBinding::Bool;
    assert!(boolean_p.is_ok());
    assert_eq!(boolean_p.unwrap(), boolean);

    // Test Char
    let charector_p = TypeBinding::from_str("Char");
    let charector = TypeBinding::Char;
    assert!(charector_p.is_ok());
    assert_eq!(charector_p.unwrap(), charector);

    // Test Str
    let stri_p = TypeBinding::from_str("Str");
    let stri = TypeBinding::Str;
    assert!(stri_p.is_ok());
    assert_eq!(stri_p.unwrap(), stri);

    // Test Unit
    let unit_p = TypeBinding::from_str("Unit");
    let unit = TypeBinding::Unit;
    assert!(unit_p.is_ok());
    assert_eq!(unit_p.unwrap(), unit);

    // Test Star
    let int_star_p = TypeBinding::from_str("*Int");
    let int_star = TypeBinding::Star(Box::new(TypeBinding::Int));
    assert!(int_star_p.is_ok());
    assert_eq!(int_star_p.unwrap(), int_star);
    assert!(TypeBinding::from_str("**Int").is_err());

    // Test Arrow
    let arrow_p = TypeBinding::from_str("-> Any *Char Int");
    let arrow = TypeBinding::Arrow(
      vec![
        TypeBinding::Any,
        TypeBinding::Star(Box::new(TypeBinding::Char)),
      ],
      Box::new(TypeBinding::Int),
    );
    assert!(arrow_p.is_ok());
    assert_eq!(arrow_p.unwrap(), arrow);

    assert!(TypeBinding::from_str("-> Any* Char Int").is_err());
    assert!(TypeBinding::from_str("-> Any Char Int*").is_err());
  }
}

/// Test the methods of context.
#[cfg(test)]
mod test_context {
  use super::*;
  /// Tests the declare and lookup methods.
  #[test]
  fn declare_lookup() {
    let mut c = Context::default().new_scope();
    // TODO: use a random type ~100 times
    let typ = TypeBinding::Bool;
    // TODO: use a random string
    let var = "x".to_owned();
    // declareing "x" should work on an empty scope
    assert!(c.declare(var.clone(), typ.clone()).is_ok());
    // redeclareing "x" should work not on this scope
    assert!(c.declare(var.clone(), typ.clone()).is_err());
    // Lookup should be able to find the value
    assert!(c.lookup(var.clone()).is_some());
    // Looking up "x" should give the same type stored.
    assert_eq!(c.lookup(var).unwrap(), typ);
  }

  /// This function tests these properties of the scopeing rules of a context
  /// 1. If something exists in an outer scope, then it exists in an inner scope (with the exeption of shadowing).
  /// 2. If something is declared in an inner scope, then it does not exist in the outer scope.
  /// 3. (shadowing) If something is declared in an inner scope that has the same name as
  ///    something in the outter scope, then when useing that name in the inner scope it
  ///    reffers to the thing in the inner scope and the outer scope remains unchanged.
  #[test]
  fn scope_rules() {
    let mut c = Context::default().new_scope();
    c.declare("x".to_owned(), TypeBinding::Any);
    /// Test the first property.
    fn test_1(outer_scope: &Context) {
      let inner_scope = outer_scope.new_scope();
      assert!(inner_scope.lookup("x".to_owned()).is_some());
    }
    /// Test the second property.
    fn test_2(outer_scope: &Context) {
      let mut inner_scope = outer_scope.new_scope();
      assert!(inner_scope
        .declare("y".to_owned(), TypeBinding::Any)
        .is_ok());
      assert!(outer_scope.lookup("y".to_owned()).is_none());
    }
    /// Test the third property.
    fn test_3(outer_scope: &Context) {
      let mut inner_scope = outer_scope.new_scope();
      assert!(inner_scope
        .declare("x".to_owned(), TypeBinding::Int)
        .is_ok());
      assert_ne!(
        outer_scope.lookup("x".to_owned()).unwrap(),
        inner_scope.lookup("x".to_owned()).unwrap()
      );
    }

    test_1(&c);
    test_2(&c);
    test_3(&c);
  }
}

/// Test the methods of state.
#[cfg(test)]
mod test_state {
  use super::*;
}
