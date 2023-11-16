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

#[path = "type_check.rs"]
pub mod TypeCheck;

#[path = "interpreter.rs"]
pub(crate) mod Interpreter;
// pub use Interpreter::State;

use TypeCheck::ProblemSet;
// genral imports
use anyhow::{anyhow, Result};
use nom_locate::LocatedSpan;
use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::hash::Hash;
use std::str::FromStr;
use std::sync::{Arc, Mutex};

// CONSTS
// TYPES

pub type Binding = (String, Option<TypeBinding>, Box<AST>);
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum TypeBinding {
  // todo wrap the names of the varients in an arc.
  /// Enum/Sum type (Name of overall type, Names of type variables, names of type varients)
  Enum(
    String,
    Vec<(String, u64)>,
    Vec<(String, Option<TypeBinding>)>,
  ),
  /// Type constructor application (Constructor, args)
  TypeConstructorApp(Box<TypeBinding>, Vec<TypeBinding>),
  /// Unknown normal type
  UnknownType(String),
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
  /// Type of Unit
  Unit,
  /// Type level variable  
  TypeVar((String, u64)),
  /// Type of Pair (cons, car, cdr) (Pair Int x)
  Pair(Box<TypeBinding>, Box<TypeBinding>),
  /// Type of lists (List Int)
  List(Box<TypeBinding>),
}

/// A struct that holds the types of variables and the deffinitons of constructed types.
/// If it cannot find a deffiniton in this context, it goes up one level.
#[derive(Clone, Debug)]
pub struct Context(Arc<Mutex<ContextInsides>>);

/// A helper struct for |Context|
#[derive(Clone, Debug)]
struct ContextInsides {
  /// A map between the variables and there types
  type_map: HashMap<String, TypeBinding>,
  /// A map between types and there deffiniton
  type_defn_map: HashMap<String, TypeBinding>,
  /// A ''pointer'' to the upper context
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

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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
  let mut problem_set = TypeCheck::ProblemSet::new();
  // create problem set and do simple checks
  for mut ast in asts {
    TypeCheck::type_check(&mut ast, context, &mut problem_set)?;
  }
  // type unification
  TypeCheck::type_unification(&mut problem_set)?;
  return Ok(());
}

/// Type check one expression
pub fn type_check1(input: &Span, context: &mut Context) -> Result<()> {
  todo!()
}

pub fn load_standard_library(state: &mut State, context: &mut Context) -> Result<()> {
  // load library as text
  let std_lib = repl_to_span(include_str!("std.lsp"));
  // parse text
  let parsed = Parse::parse(std_lib);
  let mut asts = match parsed {
    std::result::Result::Ok((_s, mut out)) => out,
    Err(nom::Err::Error(e)) => return Err(anyhow!("{}", e.to_string())),
    Err(nom::Err::Incomplete(_)) => return Err(anyhow!("Parseing incomplete")),
    Err(nom::Err::Failure(e)) => return Err(anyhow!("{}", e.to_string())),
  };
  // type check parsed text
  let mut problem_set = TypeCheck::ProblemSet::new();
  for mut ast in asts.iter_mut() {
    let _typed = TypeCheck::type_check(&mut ast, context, &mut problem_set)?;
  }
  TypeCheck::type_unification(&mut problem_set)?;
  // execute type checked things
  for mut ast in asts.into_iter() {
    let _out = Interpreter::interperate(&mut ast, state)?;
  }
  Ok(())
}

/// run a slice of inputs through the parser, concatenate them and then type check and run the code.
pub fn run(input: &[String], state: &mut State, context: &mut Context) -> Result<Value> {
  let mut ret = Value::Unit;
  let mut asts: Vec<AST> = parse_files(input)?;
  let mut problem_set = TypeCheck::ProblemSet::new();
  // @TODO: type check asts
  for mut ast in asts.iter_mut() {
    TypeCheck::type_check(&mut ast, context, &mut problem_set)?;
  }
  TypeCheck::type_unification(&mut problem_set)?;
  for ast in asts {
    ret = Interpreter::interperate(&ast, state)?;
  }
  return Ok(ret);
}

pub fn run1(input: &Span, state: &mut State, context: &mut Context) -> Result<Value> {
  let mut parsed = parse_expr(input)?;
  let mut problem_set = TypeCheck::ProblemSet::new();
  TypeCheck::type_check(&mut parsed, context, &mut problem_set)?;
  TypeCheck::type_unification(&mut problem_set)?;
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

  /// Declare a new type deffinition in scope
  /// Errors if variable already exists
  pub fn define_type(&mut self, var: String, typ: TypeBinding) -> Result<()> {
    let Context(ref mut insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().define_type(var, typ)
  }

  /// Find the type for a definition in scope
  pub fn lookup_type(&self, var: String) -> Option<TypeBinding> {
    let Context(ref insides) = self;
    // TODO find a way around unwrap
    insides.lock().unwrap().lookup_type(var)
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
      type_defn_map: HashMap::new(),
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
  /// Declare a new type deffinition in scope
  /// Errors if variable already exists
  pub fn define_type(&mut self, var: String, typ: TypeBinding) -> Result<()> {
    match self.type_defn_map.get(&var) {
      Some(_) => Err(anyhow!("Type \"{var}\" already declared in current scope")),
      None => {
        self.type_map.insert(var, typ);
        Ok(())
      }
    }
  }

  /// Find the type for a definition in scope
  pub fn lookup_type(&self, var: String) -> Option<TypeBinding> {
    match self.type_defn_map.get(&var) {
      // return value in current scope
      Some(x) => Some(x.to_owned()),
      // return value in higher scope
      None => match &self.up_scope {
        Some(scope) => scope.lookup_type(var),
        None => None,
      },
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
    let init_con = Builtin::inital_context();
    Self {
      type_map: init_con.0,
      type_defn_map: init_con.1,
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
  /// substitutes unknown types iff they have a deffinition in context
  /// in the case of an unknonPtype, add problems to the problem set to make it correct
  /// Returns an error if an unknown type was found, but has no deffinition in context
  /// or the wrong number of arguments were suplied
  pub fn substitute_unknown(
    &mut self,
    context: &mut Context,
    problem_set: &mut ProblemSet,
  ) -> Result<()> {
    match self {
      TypeBinding::UnknownType(name) => {
        if let Some(typ) = context.lookup_type(name.to_string()) {
          // check that if typ is a type Constructor, it has 0 arguments
          match typ {
            TypeBinding::Enum(ref e_name, ref type_vars, ref _bindings) => {
              if type_vars.len() != 0 {
                return Err(anyhow!("Wrong number of arguments supplied to type constructor {e_name}, expected 0, found {}", type_vars.len()));
              }
            }
            _ => (),
          };
          *self = typ;
        } else {
          return Err(anyhow!("could not find the type {name} in current context, if this is ment to be a type variable it must be 1 charector long"));
        }
      }
      TypeBinding::TypeConstructorApp(ref mut constructor, ref mut args) => {
        for arg in args {
          arg.substitute_unknown(context, problem_set)?;
        }
        constructor.substitute_unknown(context, problem_set)?;
      }
      TypeBinding::Arrow(ref mut args, ref mut ret_typ) => {
        for arg in args {
          arg.substitute_unknown(context, problem_set)?;
        }
        ret_typ.substitute_unknown(context, problem_set)?;
      }
      TypeBinding::Enum(_name, _type_vars, ref mut constructors) => {
        for (_name, opt_typ) in constructors {
          if let Some(ref mut typ) = opt_typ {
            typ.substitute_unknown(context, problem_set)?
          }
        }
      }
      TypeBinding::List(ref mut typ) => {
        typ.substitute_unknown(context, problem_set)?;
      }
      TypeBinding::Pair(ref mut typ1, ref mut typ2) => {
        typ1.substitute_unknown(context, problem_set)?;
        typ2.substitute_unknown(context, problem_set)?;
      }
      TypeBinding::Star(ref mut typ) => {
        typ.substitute_unknown(context, problem_set)?;
      }
      _ => (),
    };
    Ok(())
  }

  /// returns the type vaiables used within the type
  pub fn get_type_vars(&self) -> HashSet<(String, u64)> {
    let mut ret: HashSet<(String, u64)> = HashSet::new();
    match self {
      TypeBinding::Arrow(ref args, ref ret_typ) => {
        for arg in args {
          ret = ret.union(&arg.get_type_vars()).cloned().collect();
        }
        ret = ret.union(&ret_typ.get_type_vars()).cloned().collect();
      }
      TypeBinding::Enum(_name, type_vars, _constructors) => {
        // I don't need to look in the constructors because Enums
        // are only allowed to have type variables declared in the typevars space.
        ret = ret
          .union(&type_vars.iter().cloned().collect())
          .cloned()
          .collect();
      }
      TypeBinding::List(typ) => {
        ret = ret.union(&typ.get_type_vars()).cloned().collect();
      }
      TypeBinding::Pair(typ1, typ2) => {
        ret = ret.union(&typ1.get_type_vars()).cloned().collect();
        ret = ret.union(&typ2.get_type_vars()).cloned().collect();
      }
      TypeBinding::Star(typ) => {
        ret = ret.union(&typ.get_type_vars()).cloned().collect();
      }
      TypeBinding::TypeConstructorApp(cons, ref args) => {
        for arg in args {
          ret = ret.union(&arg.get_type_vars()).cloned().collect();
        }
        ret = ret.union(&cons.get_type_vars()).cloned().collect();
        ()
      }
      TypeBinding::TypeVar(v) => {
        ret.insert(v.clone());
      }
      // TypeBinding::&UnknownType
      _ => (),
    }
    return ret;
  }
  /// returns true if the type is a function type
  pub fn is_function(&self) -> bool {
    match self {
      &TypeBinding::Arrow(_, _) => true,
      _ => false,
    }
  }
  /// Returns true if the type is a star type (e.x. *Int)
  pub fn is_star(&self) -> bool {
    match self {
      TypeBinding::Star(_) => true,
      _ => false,
    }
  }
  /// updates the type variables in the type
  /// to be in a new scope.
  /// used on the types of functions durring
  /// function application to avoid occours check failures
  /// during unification (example (car (car x)) =>
  /// (-> (Pair x y) x) (-> (Pair x y) x)  leads to x occours in (Pair x y) errors).
  pub fn new_type_var_scope(&self) -> Self {
    let scope_number = Parse::get_new_typevar_scope();
    self.set_type_var_scope(scope_number)

}

    /// sets the type var scope number
    pub fn set_type_var_scope(&self,scope_number: u64) -> Self {
    // let scope_number = Parse::get_new_typevar_scope();
    fn new_scope_helper(x: &mut TypeBinding, scope_number: u64) {
      match x {
        TypeBinding::Any => (),
        TypeBinding::Int => (),
        TypeBinding::Bool => (),
        TypeBinding::Char => (),
        TypeBinding::Str => (),
        TypeBinding::Unit => (),
        TypeBinding::UnknownType(_) => (),
        TypeBinding::Enum(_name, ref mut typ_vars, _opt_typ) => {
          for (_name, ref mut num) in typ_vars {
            *num = scope_number;
          }
        }
        TypeBinding::TypeConstructorApp(ref mut cons, ref mut typ_args) => {
          new_scope_helper(cons, scope_number);
          for ref mut typ in typ_args {
            new_scope_helper(typ, scope_number);
          }
        }
        TypeBinding::Star(ref mut a) => new_scope_helper(a, scope_number),
        TypeBinding::List(ref mut a) => new_scope_helper(a, scope_number),
        TypeBinding::Pair(ref mut a, ref mut b) => {
          new_scope_helper(a, scope_number);
          new_scope_helper(b, scope_number);
        }
        TypeBinding::Arrow(ref mut args, ref mut ret) => {
          for mut a in args {
            new_scope_helper(&mut a, scope_number);
          }
          new_scope_helper(ret, scope_number);
        }
        TypeBinding::TypeVar((_, ref mut num)) => {
          *num = scope_number;
        }
      }
    }

    let mut x = self.clone();
    new_scope_helper(&mut x, scope_number);
    x
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
      List(body) => write!(f, "(List {body})"),
      Pair(car, cdr) => write!(f, "(Pair {car} {cdr})"),
      TypeVar(x) => write!(f, "{}", x.0),
      Star(body) => write!(f, "*{body}"),
      TypeBinding::UnknownType(name) => write!(f, "{name}"),
      TypeBinding::TypeConstructorApp(name, typ_args) => {
        write!(f, "({name} ")?;
        for typ in typ_args {
          write!(f, "{typ} ")?;
        }
        write!(f, ") ")
      }
      Enum(name, typ_vars, varients) => {
        write!(f, "(Enum {name} ");
        write!(f, "[ ")?;
        for var in typ_vars {
          write!(f, "{}, ", var.0)?;
        }
        write!(f, " ] ")?;
        for (name, typ) in varients {
          if let Some(typ) = typ {
            write!(f, "({name} {typ}) ")?;
          } else {
            write!(f, "({name} ) ")?;
          }
        }
        write!(f, ")")
      }
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
    // Test TypeVar
    let typ_var_p1 = TypeBinding::from_str("x");
eprintln!("{typ_var_p1:?}");
    let typ_var_p2 = TypeBinding::from_str("y");
    let mut scope1: u64 = 0;
    assert!(typ_var_p1.is_ok());
    assert!(typ_var_p2.is_ok());
    assert!(match typ_var_p1 {
      Ok(TypeBinding::TypeVar((x, scope))) => {
        scope1 = scope;
        x == "x".to_owned()
      }
      _ => false,
    });
    assert!(match typ_var_p2 {
      Ok(TypeBinding::TypeVar((y, scope))) => {
        scope1 != scope && y == "y".to_owned()
      }
      _ => false,
    });
    assert!(TypeBinding::from_str("x[").is_err());

    // Test Pair
    let pair_p = TypeBinding::from_str("(Pair Int Unit)");
    let pair = TypeBinding::Pair(Box::new(TypeBinding::Int), Box::new(TypeBinding::Unit));
    assert!(pair_p.is_ok());
    assert_eq!(pair_p.unwrap(), pair);
    assert!(TypeBinding::from_str("(Pair Int *Unit)").is_err());
    assert!(TypeBinding::from_str("(Pair *Int Unit)").is_err());
    assert!(TypeBinding::from_str("(Pair *Int *Unit)").is_err());

    // Test List
    let list_p = TypeBinding::from_str("(List Str)");
    let list = TypeBinding::List(Box::new(TypeBinding::Str));
    assert!(list_p.is_ok());
    assert_eq!(list_p.unwrap(), list);
    assert!(TypeBinding::from_str("(List *Int)").is_err());

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

    assert!(TypeBinding::from_str("-> *Any Char Int").is_err());
    assert!(TypeBinding::from_str("-> Any Char *Int").is_err());

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
