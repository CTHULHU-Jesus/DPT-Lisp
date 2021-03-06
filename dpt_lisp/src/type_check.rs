// IMPORTS
use super::{
  Binding, Context, ErrorKind, FileLocation, MyError, Parse::LFunction, Span, State, TypeBinding,
  Value, AST,
};
use anyhow::{anyhow, Result};

// CONSTS
// TYPES

#[derive(Debug)]
pub enum TypeError {
  Mismatch(String, TypeBinding, TypeBinding),
  NoVar(String),
  CallOfNonFunc(TypeBinding),
  EmpySEpr,
  StarNotAtEnd,
  Other(anyhow::Error),
}
// FUNCTIONS

/// Turn anyhow error into a MyError
pub fn to_myerror<T>(x: Result<T>, loc: &FileLocation) -> Result<T, MyError> {
  x.map_err(|e: anyhow::Error| {
    let x: TypeError = e.into();
    x.into_myerror(loc)
  })
}
/// check the types and fill in the important type bindings where the user did not write them
pub fn type_check(input: &mut AST, context: &mut Context) -> Result<TypeBinding, MyError> {
  match input {
    AST::Fun(ref mut f, loc) => to_myerror(type_of_function(f, context), &loc),
    AST::Val(ref mut val, loc) => to_myerror(type_of_value(val, context), &loc),
    AST::Var(name, loc) => context
      .lookup(name.clone())
      .ok_or(TypeError::NoVar(name.clone()).into_myerror(loc)),
    AST::Let(ref mut bindings, ref mut body, _loc) => {
      let mut new_context = context.new_scope();
      apply_bindings(bindings, &mut new_context)?;
      // the let expression returns the last thing in the body
      body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
        type_check(ast, &mut new_context)
      })
    }
    AST::Define(ref mut binding, _loc) => {
      apply_binding(binding, context)?;
      // can use unwrap here because apply binding enuses it will be Some(_)
      Ok(binding.1.clone().unwrap())
    }
    AST::Set(name, ref mut val, loc) => {
      let b_typ = type_check(val, context)?;
      let typ = context
        .lookup(name.to_string())
        .ok_or(TypeError::NoVar(name.to_string()).into_myerror(loc))?;
      // make shure the types match
      if !typ.same_as(b_typ.clone(), &context) {
        return Err(TypeError::Mismatch(name.clone(), typ, b_typ).into_myerror(loc));
      }
      // set returns the value set
      return Ok(typ);
    }
    AST::Sexpr(ref mut asts, loc) => {
      // check that the expession is not empy
      if asts.len() < 1 {
        return Err(TypeError::EmpySEpr.into_myerror(loc));
      }
      // get the type of the function
      match type_check(&mut asts[0], context)? {
        TypeBinding::Arrow(a_args, a_ret) => {
          let b_args = asts[1..]
            .iter_mut()
            .map(|ast: &mut AST| type_check(ast, context))
            .collect::<Result<Vec<TypeBinding>, MyError>>()?;
          function_application_check(&a_args, &b_args, context).map_err(|e| e.into_myerror(loc))?;
          Ok(*a_ret.clone())
        }
        x => return Err(TypeError::CallOfNonFunc(x).into_myerror(loc)),
      }
    }
  }
}

/// check if function application args type check
/// Also checks if there is a Star type, that it is at the end
/// |a_args|: the arguments the function needs to be applied
/// |b_args|: the arguments trying to be applied to the function
fn function_application_check(
  a_args: &[TypeBinding],
  b_args: &[TypeBinding],
  context: &mut Context,
) -> Result<(), TypeError> {
  // Pop types off of a_args and b_args.
  // Unless the current a type is a star type,
  // then just pop b_args untill empty.
  // If there is a star type, it must be in
  // a_args and at the end.
  let mut a_args: Vec<TypeBinding> = a_args.iter().cloned().collect::<Vec<_>>();
  let mut b_args: Vec<TypeBinding> = b_args.iter().cloned().collect();
  // reverse because Vec's pop from the back.
  a_args.reverse();
  b_args.reverse();
  let mut a: Option<TypeBinding> = None;
  while b_args.is_empty() == false {
    a = match &a {
      Some(x) if x.is_star() => a,
      _ => Some(a_args.pop().ok_or_else(|| {
        // println!("too many args");
        anyhow!("too many arguments applied to function.").into()
      })?),
    };
    // star check for a
    if a.as_ref().unwrap().is_star() && a_args.len() != 0 {
      // println!("wrong star placement");

      return Err(anyhow!("Star types must come at the end of arguments.").into());
    }

    // b_args is verrified not to be empty
    let b = b_args.pop().unwrap();
    // verrify that b can be coerced to a.
    println!("a:{a:?}, b:{b}");
    if !a.as_ref().unwrap().same_as(b.clone(), context) {
      // println!("bad types");
      return Err(anyhow!("{} could not be coerced to {b}", a.unwrap()).into());
    }
  }
  // If a_args has more elemets, it should only be one Star type
  if (a_args.len() == 1 && !a_args[0].is_star()) || a_args.len() > 1 {
    return Err(anyhow!("Applied wrong number of args").into());
  }
  Ok(())
}

/// apply one binding, and set the type of the binding to Some(_) if it was None.
fn apply_binding(bind: &mut Binding, context: &mut Context) -> Result<(), MyError> {
  let (name, ref mut typ, ref mut body) = bind;
  // type of the body
  let b_typ = type_check(body, context)?;
  // set type if it does not exist
  if typ.is_none() {
    *typ = Some(b_typ.clone());
  } else {
    // if it does, make shure it matches
    if !typ.as_ref().unwrap().same_as(b_typ.clone(), context) {
      //
      return Err(
        TypeError::Mismatch(name.to_owned(), typ.clone().unwrap(), b_typ)
          .into_myerror(&body.position()),
      );
    }
  }
  // If it passes, add it to the context
  to_myerror(context.declare(name.to_owned(), b_typ), &body.position())?;
  Ok(())
}

/// Apply bindings
fn apply_bindings(bindings: &mut Vec<Binding>, context: &mut Context) -> Result<(), MyError> {
  for mut bind in bindings {
    apply_binding(&mut bind, context)?;
  }
  Ok(())
}

/// Find the type of values
/// TODO: finish when type system can suport more
fn type_of_value(val: &mut Value, context: &mut Context) -> Result<TypeBinding> {
  Ok(match val {
    Value::Char(_) => TypeBinding::Char,
    Value::Int(_) => TypeBinding::Int,
    Value::Str(_) => TypeBinding::Str,
    Value::Bool(_) => TypeBinding::Bool,
    Value::Unit => TypeBinding::Unit,
    Value::Fun(ref mut f, _) => type_of_function(f, context)?,
    Value::Meval(_, _) => todo!(),
    Value::Pair(_, _) => todo!(),
    Value::List(_) => todo!(),
  })
}
/// Returns the type of a function
fn type_of_function(f: &mut LFunction, context: &mut Context) -> Result<TypeBinding> {
  match f {
    LFunction::BuiltinF(name, _) | LFunction::BuiltinM(name, _) => {
      Ok(context.lookup(name.to_string()).unwrap())
    }
    LFunction::LambdaF(args, body) | LFunction::LambdaM(args, body) => {
      // list of arg types in arrow type
      let mut types = vec![];
      let mut new_context = context.new_scope();
      //add variable to context
      for (name, typ) in args {
        types.append(&mut vec![typ.clone()]);
        new_context.declare(name.to_string(), typ.to_owned())?;
      }
      // get the return type of the function
      let ret: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
        type_check(&mut *ast, &mut new_context)
      })?;
      Ok(TypeBinding::Arrow(types, Box::new(ret)))
    }
  }
}
// TRAITS
// IMPLS

impl Into<TypeError> for anyhow::Error {
  fn into(self) -> TypeError {
    TypeError::Other(self)
  }
}

impl TypeError {
  pub fn into_myerror(&self, loc: &FileLocation) -> MyError {
    let message: String = match self {
      TypeError::Mismatch(var, expected, found) => {
        format!("{var} has wrong type, expected {expected}, found {found}")
      }
      TypeError::NoVar(var) => format!("\"{var}\" does not exist in current scope"),
      TypeError::Other(e) => format!("{e}"),
      TypeError::CallOfNonFunc(x) => {
        format!("{x} is not a function type and can't have arguments applied to it")
      }
      TypeError::EmpySEpr => "Empty S-expression, needs a funtion with arguments".to_owned(),
      TypeError::StarNotAtEnd => "Star types only aloud at the end".to_owned(),
    };

    MyError::new(ErrorKind::TypeCheck(message), loc.to_owned())
  }
}

// TESTS
#[cfg(test)]
mod test {
  #[test]
  fn test_function_application() {
    use super::{function_application_check, Context, TypeBinding::*};
    // test1
    let test1 = vec![Int, Int, Str, Star(Box::new(Bool))];
    // test1.1
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str],
      &mut Context::default()
    )
    .is_ok());
    // test1.2
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool],
      &mut Context::default()
    )
    .is_ok());
    // test1.3
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool, Bool, Bool],
      &mut Context::default()
    )
    .is_ok());
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool],
      &mut Context::default()
    )
    .is_ok());
    // test 2
    let test2 = vec![Star(Box::new(Str)), Char];
    // test 2.1
    assert!(function_application_check(&test2, &vec![Str, Char], &mut Context::default()).is_err());
    assert!(function_application_check(&test2, &vec![Char, Int], &mut Context::default()).is_err());
  }
}
