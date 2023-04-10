// IMPORTS
use super::{Binding, ErrorKind, FileLocation, IResult, InputOrigin, Interpreter, MyError, Span, State, TypeBinding,}; use anyhow::{anyhow, Result}; use lazy_static::lazy_static; use nom::{branch::alt, bytes::complete::tag, character::complete::*, combinator::{cut, map, opt, peek},
  multi::{many0, many1},
  InputIter,
};
use nom_locate::position;
use std::{collections::VecDeque, fmt::Display, i128, string, sync::Arc};

// CONSTS
/// List of characters that count as whitespace. Stolen from https://doc.rust-lang.org/reference/whitespace.html
const WHITESPACE: &str =
  "\u{0009}\u{000A}\u{000B}\u{000C}\u{000D}\u{0020}\u{0085}\u{200E}\u{200F}\u{2028}\u{2029}";
lazy_static! {
    static ref __RESTRICTED_CHARS: String = vec!["()'#[]\".", WHITESPACE].join("");
    /// List of characters that cant be used in variable names
    static ref RESTRICTED_CHARS: &'static str = __RESTRICTED_CHARS.as_str();
    static ref __RESTRICTED_CHARS_WITH_NUMBERS__ : String = [*RESTRICTED_CHARS,"0123456789"].join("");
    /// List of characters that cant be used in variable names including 0-9
    static ref RESTRICTED_CHARS_WITH_NUMBERS : &'static str= __RESTRICTED_CHARS_WITH_NUMBERS__.as_str();
}
// TYPES
#[derive(Clone, Debug)]
/// Abstract syntax tree for language
pub enum AST {
  /// Node to hold functions (bultins and lambdas)
  Fun(LFunction, FileLocation),
  /// Node to hold let expressions
  Let(Vec<Binding>, Vec<AST>, FileLocation),
  /// Node to hold a s-expression
  Sexpr(Vec<AST>, FileLocation),
  /// Node to hold a variable
  Var(String, FileLocation),
  /// Node to hold a value that needs no more evaluation
  Val(Value, FileLocation),
  /// Add a variable (with value ) to current scope
  Define(Binding, FileLocation),
  /// Node that lets you define mutual recursive functions
 LetRec(Vec<Binding>, Vec<AST>, FileLocation),
  /// Node for createing an Enum (Sum Types)
  Enum(String, Vec<(String, u64)>, Vec<(String, Option<TypeBinding>)>, FileLocation),
  /// Match statement for unpacking enums
  Match(Box<AST>, Vec<(MatchCondition, Vec<AST>)>, FileLocation),
  /// Set pre defined variable with a value
  Set(String, Box<AST>, FileLocation),
}

#[derive(Clone, Debug)]
/// condition for a match
pub enum MatchCondition {
  /// constant value (constructor name, value)
  Const(String, Option<AST>),
  /// single variable (construcor name, var name)
  SingleV(String, String),
  /// Default condition
  Default,
}

/// LBuiltinF (Lisp builtin) is the function pointer type
pub type LBuiltinF = fn(&mut Vec<Value>) -> Result<Value>;

/// LBuiltinM (Lisp builtin) is the function pointer type that
/// can act as a macro
pub type LBuiltinM = fn(&mut State, &mut Vec<AST>) -> Result<Value, MyError>;

/// There are two types of function - builtin and lambda
#[derive(Clone)]
pub enum LFunction {
  /// Enum/Sum type constructor (enum constructor name, optional type contained)
  EnumConstructor(String, Option<TypeBinding>),
  /// (name, function pointer)
  BuiltinF(String, LBuiltinF),
  /// (name, function pointer)
  BuiltinM(String, LBuiltinM),
  /// lambda function (args, return type ,body), args are a list of variable names and types
  LambdaF(Vec<(String, TypeBinding)>, Option<TypeBinding>, Vec<AST>),
  /// lambda lazy (args, return type, body), args are a list of variable names  and types
  LambdaL(Vec<(String, TypeBinding)>, Option<TypeBinding>, Vec<AST>),
}

#[derive(Clone, Debug)]
pub enum Value {
  /// enum constructed value (constructor name, value)
  EnumVal(String, Option<Box<Value>>),
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
  /// A unit value
  Unit,
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

/// identifier parser
fn identifier(s: Span) -> IResult<String> {
  let (s, fst_char) = none_of(*RESTRICTED_CHARS_WITH_NUMBERS)(s)?;
  let (s, mut rest) = many1(none_of(*RESTRICTED_CHARS))(s)?;
  rest.insert(0, fst_char);
  let var: String = rest.into_iter().collect();
  return IResult::Ok((s, var));
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
  let (s, e) = alt((
    lambda, define, enum_expr, match_expr, set, let_expr, expr, value, variable,
  ))(s)?;
  let (s, _) = whitespace(s)?;
  return IResult::Ok((s, e));
}

/// Parse annonamas functions
fn lambda(s: Span) -> IResult<AST> {
  fn var(s: Span) -> IResult<(String, TypeBinding)> {
    let (s, _) = whitespace(s)?;
    let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
    let (s, _) = whitespace(s)?;
    // TODO throw custom error about missing type bindings
    let (s, typ) = type_binding(s)?;
    let var: String = var.into_iter().collect();
    return IResult::Ok((s, (var, typ)));
  }
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  // macro or function
  let (s, kind) = alt((tag("llambda"), tag("lλ"), tag("λ"), tag("lambda")))(s)?;
  let (s, _) = whitespace(s)?;
  let (s, ret_typ) = opt(type_binding)(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char('(')(s)?;
  let (s, args) = many0(var)(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char(')')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, body) = many1(all_expr)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  // If function
  if vec!["λ", "lambda"].contains(&kind) {
    return IResult::Ok((
      s,
      AST::Fun(LFunction::LambdaF(args, ret_typ, body), location),
    ));
  } else {
    // If macro
    return IResult::Ok((
      s,
      AST::Fun(LFunction::LambdaL(args, ret_typ, body), location),
    ));
  }
}

/// Parse a match expression
fn match_expr(s: Span) -> IResult<AST> {
  fn match_condition(s: Span) -> IResult<MatchCondition> {
    fn const_cond(s: Span) -> IResult<MatchCondition> {
      let (s, constructor) = many1(none_of(*RESTRICTED_CHARS))(s)?;
      let (s, _) = whitespace(s)?;
      let (s, v) = peek(opt(tag(")")))(s)?;
      let constructor: String = constructor.into_iter().collect();
      if let Some(_) = v {
        return IResult::Ok((s, MatchCondition::Const(constructor, None)));
      } else {
        let (s, val) = value(s)?;
        return IResult::Ok((s, MatchCondition::Const(constructor, Some(val))));
      }
    }
    fn single_var(s: Span) -> IResult<MatchCondition> {
      let (s, constructor) = many1(none_of(*RESTRICTED_CHARS))(s)?;
      let (s, _) = whitespace(s)?;
      let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
      let constructor: String = constructor.into_iter().collect();
      let var: String = var.into_iter().collect();
      return IResult::Ok((s, MatchCondition::SingleV(constructor, var)));
    }
    fn default(s: Span) -> IResult<MatchCondition> {
      let (s, _) = tag("default")(s)?;
      return IResult::Ok((s, MatchCondition::Default));
    }
    let (s, _) = char('(')(s)?;
    let (s, _) = whitespace(s)?;
    let (s, x) = alt((default, const_cond, single_var))(s)?;
    let (s, _) = whitespace(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = whitespace(s)?;
    return IResult::Ok((s, x));
  }
  fn match_row(s: Span) -> IResult<(MatchCondition, Vec<AST>)> {
    let (s, _) = char('(')(s)?;
    let (s, _) = whitespace(s)?;
    let (s, cond) = match_condition(s)?;
    let (s, body) = many1(all_expr)(s)?;
    let (s, _) = whitespace(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = whitespace(s)?;
    return IResult::Ok((s, (cond, body)));
  }
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = tag("match")(s)?;
  let (s, _) = whitespace(s)?;
  let (s, input) = all_expr(s)?;
  let (s, _) = whitespace(s)?;
  let (s, conditions) = many1(match_row)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  return IResult::Ok((s, AST::Match(Box::new(input), conditions, location)));
}

/// Parse an Enum expression
fn enum_expr(s: Span,) -> IResult<AST> {
  fn elem(s: Span,scope_number:u64) -> IResult<(String, Option<TypeBinding>)> {
    let (s, _) = char('(')(s)?;
    let (s, _) = whitespace(s)?;
    let (s, var) = identifier(s)?;
    let (s, _) = whitespace(s)?;
    let (s, typ) = opt(type_binding)(s)?;
    let (s, _) = whitespace(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = whitespace(s)?;
    // let var: String = var.into_iter().collect();
    return IResult::Ok((s, (var, typ.map(|t| t.set_type_var_scope(scope_number)))));
  }
  fn type_vars(s: Span,varNum: u64) -> IResult<Vec<(String,u64)>> {
todo!()
} 

  let scope_number = get_new_typevar_scope();
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = tag("enum")(s)?;
  let (s, _) = whitespace(s)?;
  // name
  let (s, name) = identifier(s)?;
  let (s, _) = whitespace(s)?;
  // TypeVars
let (s, type_vars_vec) = type_vars(s,scope_number)?;
  let (s, _) = whitespace(s)?;
  // constructors
  let (s, elems) = many1(|s| elem(s,scope_number))(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  // let name: String = name.into_iter().collect();
  return IResult::Ok((s, AST::Enum(name, type_vars_vec, elems, location)));
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
  let (s, typ) = opt(type_binding)(s)?;
  let (s, body) = all_expr(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  let var: String = var.into_iter().collect();
  return IResult::Ok((s, AST::Define((var, typ, Box::new(body)), location)));
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
  fn binding(s: Span) -> IResult<Binding> {
    let (s, _) = char('(')(s)?;
    let (s, _) = whitespace(s)?;
    let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
    let (s, _) = whitespace(s)?;
    let (s, typ) = opt(type_binding)(s)?;
    let (s, body) = all_expr(s)?;
    let (s, _) = whitespace(s)?;
    let (s, _) = char(')')(s)?;
    let (s, _) = whitespace(s)?;
    let var: String = var.into_iter().collect();
    return IResult::Ok((s, (var, typ, Box::new(body))));
  }
  let (s, pos1) = position(s)?;
  let (s, _) = char('(')(s)?;
  let (s, _) = whitespace(s)?;
  let (s, let_typ) = alt((tag("let"), tag("letrec")))(s)?;
  let (s, _) = whitespace(s)?;
  let (s, _) = char('(')(s)?;
  let (s, bindings) = many0(binding)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, body) = many1(all_expr)(s)?;
  let (s, _) = char(')')(s)?;
  let (s, pos2) = position(s)?;
  let (s, _) = whitespace(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  if let_typ.to_string() == "let" {
    return IResult::Ok((s, AST::Let(bindings, body, location)));
  } else {
    return IResult::Ok((s, AST::LetRec(bindings, body, location)));
  }
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

/// Parse a variable
fn variable(s: Span) -> IResult<AST> {
  let (s, pos1) = position(s)?;
  let (s, var) = many1(none_of(*RESTRICTED_CHARS))(s)?;
  let (s, pos2) = position(s)?;
  let location = FileLocation::new(pos1, Some(pos2));
  let var: String = var.iter().collect();
  let node = AST::Var(var, location);

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
  fn unit(s: Span) -> IResult<Value> {
    let (s, _) = tag("unit")(s)?;
    return IResult::Ok((s, Value::Unit));
  }
  let (s, pos1) = position(s)?;
  let (s, value) = alt((unit, boolean, integer, charector, my_string))(s)?;
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
/// generates a new number whenever called
/// used to give each type binding its own scope
pub fn get_new_typevar_scope() -> u64 {
  unsafe {
    static mut x: u64 = 0;
    x += 1;
    x
  }
}

/// Parse a type binding
/// e.x. [-> Int Int Int] for a function
/// [Int] for an integer
/// [-> *String String] any number of strings to one string
pub fn type_binding(s: Span) -> IResult<TypeBinding> {
  use TypeBinding::*;
  static mut scope_num: u64 = 0;
  unsafe {
    // get new scope number
    scope_num = get_new_typevar_scope();
  }
  fn any_type(s: Span) -> IResult<TypeBinding> {
    // any type (Any)
    fn any(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Any")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Any));
    }
    // Integer type (Int)
    fn int(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Int")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Int));
    }
    // Boolean type (Bool)
    fn boolean(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Bool")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Bool));
    }
    // Function/Macro type (args types,return type) (-> x x y)
    fn arrow(s: Span) -> IResult<TypeBinding> {
      /// Checks that, if there is a * type, it is at the end.
      fn check_star(args: &[TypeBinding]) -> bool {
        for (num, arg) in args.into_iter().enumerate() {
          if arg.is_star() && (num + 1) != args.len() {
            return false;
          }
        }
        return true;
      }
      let (s, pos1) = position(s)?;
      let (s, _) = tag("->")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, body) = many1(any_type)(s)?;
      let (s, pos2) = position(s)?;
      let mut body: VecDeque<TypeBinding> = body.into_iter().collect();
      // last type is the return types
      // can unwrap because I used many1 earlyer
      let ret = body.pop_back().unwrap();
      // all but the last type are args types
      let args: Vec<_> = body.into_iter().collect();
      // check that, if there is a star type it is last
      // also no returning star types
      if check_star(&args) == false || ret.is_star() {
        return IResult::Err(nom::Err::Failure(MyError::new_from_span(
          ErrorKind::Parse,
          pos1,
          Some(pos2),
        )));
      }
      return IResult::Ok((s, Arrow(args, Box::new(ret))));
    }
    // Star type (*x)
    fn star(s: Span) -> IResult<TypeBinding> {
      let (s, pos1) = position(s)?;
      let (s, _) = tag("*")(s)?;
      let (s, body) = any_type(s)?;
      let (s, pos2) = position(s)?;
      let (s, _) = whitespace(s)?;
      // Check that the body is not a star type
      if body.is_star() {
        return IResult::Err(nom::Err::Failure(MyError::new_from_span(
          ErrorKind::Parse,
          pos1,
          Some(pos2),
        )));
      }
      return IResult::Ok((s, Star(Box::new(body))));
    }
    // Charector type (Char)
    fn charector(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Char")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Char));
    }
    // The string type (Str)
    fn string(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Str")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Str));
    }
    // type of Unit
    fn unit(s: Span) -> IResult<TypeBinding> {
      let (s, _) = tag("Unit")(s)?;
      let (s, _) = whitespace(s)?;
      return IResult::Ok((s, Unit));
    }
    // parentheses around one type or more
    // produces an UnknownPType(String, Vec<TypeBinding>),
    // iff and only if there is more than one type
    fn parens(s: Span) -> IResult<TypeBinding> {
      let (s, pos1) = position(s)?;
      let (s, _) = tag("(")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, bodys) = many1(any_type)(s)?;
      let (s, _) = tag(")")(s)?;
      let (s, pos2) = position(s)?;
      let (s, _) = whitespace(s)?;
      if bodys.len() == 1 {
        // bodus guarentead to have at least 1
        // element because of the use of "many1"
        // in its creations.
        return IResult::Ok((s, bodys[0].clone()));
      } else {
return IResult::Ok((s,TypeBinding::TypeConstructorApp(Box::new(bodys[0].clone()), bodys[1..].to_vec())));
        // match &bodys[0] {
        //   UnknownType(name) => return IResult::Ok((s, UnknownPType(name.to_string(), bodys[1..].to_vec()))),
        //   _ => {
        //     return IResult::Err( nom::Err::Failure(MyError::new_from_span(
        //       ErrorKind::TypeCheck("Wrong application of types.".to_string()),
        //       pos1,
        //       Some(pos2),
        //     )))
        //   }
        // }
      }
    }
    // Type level variable or an Unknown type
    // Type level variables can only be 1 charector long
    fn type_var(s: Span) -> IResult<TypeBinding> {
      let (s, _) = whitespace(s)?;
      let (s, var) = identifier(s)?;
      let (s, _) = whitespace(s)?;
      // Type Variables are only 1 charector long
      if var.chars().count() == 1 {
        unsafe {
          return IResult::Ok((s, TypeVar((var, scope_num))));
        }
      } else {
        return IResult::Ok((s, UnknownType(var)));
      }
    }
    // Pair type
    fn pair(s: Span) -> IResult<TypeBinding> {
      let (s, _) = whitespace(s)?;
      let (s, _) = tag("(")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, _) = tag("Pair")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, pos1) = position(s)?;
      let (s, car) = any_type(s)?;
      let (s, cdr) = any_type(s)?;
      let (s, pos2) = position(s)?;
      let (s, _) = tag(")")(s)?;
      let (s, _) = whitespace(s)?;
      // car and cdr are not alowed to be a star type
      if car.is_star() || cdr.is_star() {
        return IResult::Err(nom::Err::Failure(MyError::new_from_span(
          ErrorKind::Parse,
          pos1,
          Some(pos2),
        )));
      }
      return IResult::Ok((s, TypeBinding::Pair(Box::new(car), Box::new(cdr))));
    }
    // List type
    fn list(s: Span) -> IResult<TypeBinding> {
      let (s, _) = whitespace(s)?;
      let (s, _) = tag("(")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, _) = tag("List")(s)?;
      let (s, _) = whitespace(s)?;
      let (s, pos1) = position(s)?;
      let (s, body) = any_type(s)?;
      let (s, pos2) = position(s)?;
      let (s, _) = tag(")")(s)?;
      let (s, _) = whitespace(s)?;
      // body is not alowed to be a star type
      if body.is_star() {
        return IResult::Err(nom::Err::Failure(MyError::new_from_span(
          ErrorKind::Parse,
          pos1,
          Some(pos2),
        )));
      }
      return IResult::Ok((s, TypeBinding::List(Box::new(body))));
    }
    // Do the parseing
    return alt((
      any, int, boolean, arrow, star, charector, string, unit, list, pair, parens, type_var,
    ))(s);
  }

  let (s, _) = tag("[")(s)?;
  let (s, _) = whitespace(s)?;
  let (s, binding) = any_type(s)?;
  let (s, _) = tag("]")(s)?;
  let (s, _) = whitespace(s)?;

  return IResult::Ok((s, binding));
}

// TRAITS
// IMPLS

impl MatchCondition {
  /// See if a |value| matches against condition. |loc| is the location of the match condition. If a condition is matched
  /// then the bindings are returned. If no bindings were found then an empty vector
  /// is returned.
  pub fn matchc(
    &self,
    value: Value,
    loc: &FileLocation,
    state: &mut State,
  ) -> Option<Vec<Binding>> {
    // get the value
    let (arg_constructor, arg_contents) = match value {
      Value::EnumVal(name, opt_val) => (name, opt_val),
      _ => return None,
    };
    match self {
      MatchCondition::Const(constructor, Some(val)) => {
        let contents = match val {
          AST::Val(contents, _) => contents,
          _ => return None,
        };
        if constructor == &arg_constructor
          && arg_contents.is_some()
          && contents == &*arg_contents.unwrap()
        {
          Some(vec![])
        } else {
          None
        }
      }
      MatchCondition::Const(constructor, None) => {
        if constructor == &arg_constructor {
          Some(vec![])
        } else {
          None
        }
      }
      MatchCondition::SingleV(constructor, var_name) => {
        if constructor == &arg_constructor && arg_contents.is_some() {
          Some(vec![(
            var_name.to_string(),
            None,
            Box::new(AST::Val(*arg_contents.unwrap(), loc.clone())),
          )])
        } else {
          None
        }
      }
      &MatchCondition::Default => Some(vec![]),
    }
  }
}

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
      EnumConstructor(name, _) => write!(f, "{name}"),
      BuiltinF(name, _) => write!(f, "{}", name),
      BuiltinM(name, _) => write!(f, "{}", name),
      LambdaF(args, typ, body) => {
        write!(f, "(λ ")?;
        if let Some(typ) = typ {
          write!(f, " {typ} ")?;
        }
        write!(f, "(")?;

        for (arg, typ) in args {
          write!(f, "{arg} [{typ}] ")?;
        }
        write!(f, ")")?;
        for expr in body {
          write!(f, "{expr} ")?;
        }
        write!(f, ")")
      }
      LambdaL(args, typ, body) => {
        write!(f, "(mλ ")?;
        if let Some(typ) = typ {
          write!(f, " {typ} ")?;
        }
        write!(f, "(")?;
        for (arg, typ) in args {
          write!(f, "{arg} [{typ}] ")?;
        }
        write!(f, ")")?;
        for expr in body {
          write!(f, "{expr} ")?;
        }
        write!(f, ")")
      }
    }
  }
}

impl std::fmt::Debug for LFunction {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use LFunction::*;
    match &self {
      EnumConstructor(name, opt_typ) => {
        write!(f, "lfunction::EnumConstructor({name:?},{opt_typ:?}")
      }
      BuiltinF(name, _) => write!(f, "LFunction::BultinF({name:?},function_pointer)"),
      BuiltinM(name, _) => write!(f, "LFunction::BultinM({name:?},function_pointer)"),
      LambdaF(args, typ, body) => write!(f, "LFunction::LambdaF({args:?},{typ:?},{body:?})"),
      LambdaL(args, typ, body) => write!(f, "LFunction::LambdaM({args:?},{typ:?},{body:?})"),
    }
  }
}

impl PartialEq for Value {
  fn eq(&self, other: &Self) -> bool {
    use Value::*;
    match (self, other) {
      (Char(a), Char(b)) => a == b,
      (Pair(a1, a2), Pair(b1, b2)) => a1 == b1 && a2 == b2,
      (Int(a), Int(b)) => a == b,
      (Str(a), Str(b)) => a == b,
      (List(a), List(b)) => a == b,
      (Fun(_a, _a_state), Fun(_b, _b_state)) => todo!(),
      (Bool(a), Bool(b)) => a == b,
      (Meval(_a, _a_state), Meval(_b, _b_state)) => false,
      (Unit, Unit) => true,
      _ => false,
    }
  }
}

impl Display for Value {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use Value::*;
    match self {
      EnumVal(name, val) => {
        if let Some(val) = val {
          write!(f, "({name} {val})")
        } else {
          write!(f, "({name} )")
        }
      }
      Pair(car, cdr) => write!(f, "(cons {car} {cdr})"),
      Fun(fun, _state) => write!(f, "{fun}"),
      Unit => write!(f, "unit"),
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

impl Display for MatchCondition {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use MatchCondition::*;
    match self {
      Const(name, body) => {
        if let Some(body) = body {
          write!(f, "({name} {body})")
        } else {
          write!(f, "(name )")
        }
      }
      SingleV(name, body) => write!(f, "({name} {body})"),
      Default => write!(f, "(default)"),
    }
  }
}

impl Display for AST {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      AST::Enum(name, constructors, _) => {
        write!(f, "(enum {name} ")?;
        for (constructor, typ) in constructors {
          if let Some(typ) = typ {
            write!(f, "({constructor} {typ})")?;
          } else {
            write!(f, "({constructor})")?;
          }
        }
        write!(f, ")")
      }
      AST::Match(val, conditions, _) => {
        write!(f, "(match {val} ")?;
        for (cond, body) in conditions {
          write!(f, "({cond} ")?;
          for x in body {
            write!(f, "{x} ")?;
          }
          write!(f, ")")?;
        }

        write!(f, ")")
      }
      AST::Var(a, _) => write!(f, "{a}"),
      AST::Val(a, _) => write!(f, "{a}"),
      AST::Fun(fun, _) => write!(f, "{fun}"),
      AST::Define((var, typ, def), _) => match typ {
        Some(typ) => write!(f, "(define {var} [{typ}] {def})"),
        None => write!(f, "(define {var} {def})"),
      },
      AST::Set(var, def, _) => write!(f, "(set {var} {def})"),
      AST::LetRec(bindings, body, _) => {
        write!(f, "(letrec (")?;
        for (var, typ, val) in bindings {
          match typ {
            Some(typ) => write!(f, "({var} [{typ}] {val})")?,
            None => write!(f, "({var} {val})")?,
          };
        }
        write!(f, ") ")?;
        for expr in body {
          write!(f, "{expr} ")?;
        }
        write!(f, ") ")
      }
      AST::Let(bindings, body, _) => {
        write!(f, "(let (")?;
        for (var, typ, val) in bindings {
          match typ {
            Some(typ) => write!(f, "({var} [{typ}] {val})")?,
            None => write!(f, "({var} {val})")?,
          };
        }
        write!(f, ") ")?;
        for expr in body {
          write!(f, "{expr} ")?;
        }
        write!(f, ") ")
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
      Enum(_, _, l) => l.clone(),
      Match(_, _, l) => l.clone(),
      Set(_, _, l) => l.clone(),
      Define(_, l) => l.clone(),
      Var(_, l) => l.clone(),
      Fun(_, l) => l.clone(),
      Let(_, _, l) => l.clone(),
      LetRec(_, _, l) => l.clone(),
      Val(_, l) => l.clone(),
      Sexpr(_, l) => l.clone(),
    }
  }

  pub fn as_text(&self) -> String {
    format!("{}", self)
  }
}
// TESTS
