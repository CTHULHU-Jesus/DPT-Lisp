// IMPORTS
use super::{Binding, ErrorKind, FileLocation, LFunction, MyError, Parse::AST, Span, State, Value};
use anyhow::{anyhow, Result};
use std::{error::Error, fmt::Display};

// CONSTS

// TYPES
#[derive(Debug)]
pub enum RuntimeError {
  Overflow(),
  NoVar(String),
  ExecError(anyhow::Error),
}
// FUNCTIONS

/// Turn anyhow error into a MyError
pub fn to_myerror<T>(x: Result<T>, loc: &FileLocation) -> Result<T, MyError> {
  x.map_err(|e: anyhow::Error| {
    let x: RuntimeError = e.into();
    x.into_myerror(loc)
  })
}

/// Run the interpreter on the input with given modifiable state
pub fn interperate(input: &AST, state: &mut State) -> Result<Value, MyError> {
  use AST::*;
  match input {
    Set(var, val, loc) => {
      let val: Value = interperate(val, state)?;
      to_myerror(state.assign(var.to_string(), val.clone()), loc)?;
      Ok(val)
    }
    Define((var, _, val), loc) => {
      let val: Value = interperate(val, state)?;
      to_myerror(state.declare(var.to_string(), val.clone()), loc)?;
      Ok(val)
    }
    Fun(fun, _) => Ok(Value::Fun(fun.to_owned(), state.clone())),
    Let(bindings, body, loc) => {
      let mut new_state = state.new_scope();
      to_myerror(add_bindings(bindings, &mut new_state), &loc)?;
      interperate(body, &mut new_state)
    }
    Sexpr(exprs, loc) => eval(exprs, state, &loc),
    Var(x, l) => match state.lookup(x.to_string()) {
      Some(val) => val.eval_if_needed(),
      None => Err(RuntimeError::NoVar(x.to_string()).into_myerror(l).into()),
    },
    Val(val, _) => val.eval_if_needed(),
  }
}

fn eval(exprs: &[AST], state: &mut State, loc: &FileLocation) -> Result<Value, MyError> {
  let head = interperate(&exprs[0], state)?;
  match head {
    Value::Fun(fun, mut f_state) => match fun {
      // Check for macro
      LFunction::BuiltinM(_name, m) => return m(
        state,
        &mut exprs[1..].iter().map(|x| x.to_owned()).collect(),
      ),
      LFunction::LambdaM(ref _args, ref _body) => {
        let args: Vec<Value> = exprs[1..]
          .into_iter()
          .map(|x| Value::Meval(Box::new(x.to_owned()), state.clone()))
          .collect::<Vec<Value>>();

        return apply(&fun, &args, &mut f_state, loc);
      }
				,
      // If function, evalueate args
      _ => {
        let args: Vec<Value> = exprs[1..]
          .into_iter()
          .map(|x| interperate(x, state))
          .collect::<Result<Vec<Value>, MyError>>()?;

        return apply(&fun, &args, &mut f_state, loc);
      }
    },
    _ => return Err(MyError::new(ErrorKind::Unknown, exprs[0].position()).into()),
  };
}

/// Apply a function to args with state
fn apply(
  fun: &LFunction,
  args: &[Value],
  state: &mut State,
  loc: &FileLocation,
) -> Result<Value, MyError> {
  match fun {
    LFunction::BuiltinM(_name, f) => {
      return f(
        state,
        &mut args
          .iter()
          .map(|var| AST::Val(var.clone(), loc.clone()))
          .collect(),
      );
    }
    LFunction::BuiltinF(_name, f) => {
      return to_myerror(f(&mut args.to_vec()), loc);
    }
    LFunction::LambdaF(vars, body) | LFunction::LambdaM(vars, body) => {
      // bind vars to args in new scope
      if args.len() != vars.len() {
        return Err(
          RuntimeError::ExecError(anyhow!(
            "wrong number of arguments. Expected {}, found {}.",
            vars.len(),
            args.len()
          ))
          .into_myerror(loc),
        );
      };
      let mut new_scope = state.new_scope();
      for ((var, _typ), val) in vars.into_iter().zip(args.into_iter()) {
        to_myerror(new_scope.declare(var.to_string(), val.to_owned()), loc)?;
      }
      // evaluate body
      interperate(body, &mut new_scope)
    }
  }
}

/// add bindings to state
fn add_bindings(bindings: &[Binding], state: &mut State) -> Result<()> {
  for (var, _typ, ast) in bindings {
    let val = interperate(ast, state)?;
    state.declare(var.to_string(), val)?;
  }
  Ok(())
}
// TRAITS
// IMPLS
impl RuntimeError {
  pub fn into_myerror(&self, loc: &FileLocation) -> MyError {
    let message: String = match self {
      &RuntimeError::Overflow() => "Overflow Error".to_owned(),
      RuntimeError::NoVar(s) => format!("Variable \"{s}\" not found."),
      RuntimeError::ExecError(e) => format!("{e}"),
    };
    MyError::new(ErrorKind::Runtime(message), loc.to_owned())
  }
}

impl Into<RuntimeError> for anyhow::Error {
  fn into(self) -> RuntimeError {
    RuntimeError::ExecError(self)
  }
}

// TESTS
