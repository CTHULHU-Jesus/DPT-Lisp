// IMPORTS
use super::{ErrorKind, Interpreter::State, MyError, Span, AST};
use std::{error::Error, fmt::Display};

// CONSTS
// TYPES
#[derive(Clone, Debug)]
pub enum Type {
  Int,
  Char,
  Str,
}
#[derive(Clone, Debug)]
pub enum TypeError {
  Mismatch(String, Type, Type),
  UnableToCheck(String, String),
}
// FUNCTIONS
pub fn check_types(input: &[AST], mut state: &State) -> Result<AST, MyError> {
  todo!()
}
// TRAITS
// IMPLS
impl Display for TypeError {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    todo!()
  }
}
impl Error for TypeError {
  fn source(&self) -> Option<&(dyn Error + 'static)> {
    None
  }

  //fn type_id(&self, _: private::Internal) -> std::any::TypeId
  //where
  //  Self: 'static,
  //{
  //  unsafe { std::any::TypeId::of::<Self>() }
  //}

  //  fn backtrace(&self) -> Option<&std::backtrace::Backtrace> {
  //    None
  //  }

  fn description(&self) -> &str {
    "description() is deprecated; use Display"
  }

  fn cause(&self) -> Option<&dyn Error> {
    self.source()
  }
}
// TESTS
