use crate::Parse::MatchCondition;
use std::iter::zip;

// IMPORTS
use super::{
  Binding, Context, ErrorKind, FileLocation, MyError,
  Parse::{get_new_typevar_scope, LFunction},
  Span, State, TypeBinding, Value, AST,
};
use anyhow::{anyhow, Result};
use std::{
  cmp::Reverse,
  collections::{HashMap, HashSet, VecDeque},
  convert::identity,
};

// CONSTS
// TYPES

#[derive(Debug)]
pub enum TypeError {
  Mismatch(String, TypeBinding, TypeBinding),
  LetRecFail,
  NoVar(String),
  CallOfNonFunc(TypeBinding),
  EmpySEpr,
  StarNotAtEnd,
  Other(anyhow::Error),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Individual type equations for unification algorithm
pub enum TypeEquation {
  /// Sub-type relation (SubType(a,b) == a ⊑ b == a is a sub-type of b).
  SubType(TypeBinding, TypeBinding, FileLocation),
  /// Equivalent relation (Equiv(a,b) == a=b == a is equivalent to b).
  Equiv(TypeBinding, TypeBinding, FileLocation),
  /// Or relation is true if at least one of its branches is true
  Or(Box<TypeEquation>, Box<TypeEquation>),
}

pub type ProblemSet = VecDeque<TypeEquation>;
type VarType = (String, u64);
pub type SolutionSet = HashMap<VarType, TypeBinding>;

// FUNCTIONS

/// Turn anyhow error into a MyError
pub fn to_myerror<T>(x: Result<T>, loc: &FileLocation) -> Result<T, MyError> {
  x.map_err(|e: anyhow::Error| {
    let x: TypeError = e.into();
    x.into_myerror(loc)
  })
}

/// Unifies types (e.x. " ( Pair x Int) = (Pair Unit y)" finds the solution set {x=Unit,y=Int})
/// Code based on the Robenson Algorithm, copied from the paper "Comparing Unification Algorithms in First-Order Theorem Proving"
/// By Kryˇstof Hoder and Andrei Voronkov
pub fn type_unification(p_set: &mut ProblemSet) -> Result<SolutionSet, MyError> {
  /// checks if the type variable x occours in type binding t
  /// returns true if |x| occours in |t|, false otherwise
  fn robOccursCheck(x: VarType, t: TypeBinding) -> bool {
    fn check_on_list(x: &VarType, args: &[TypeBinding]) -> bool {
      let base = false;
      args
        .into_iter()
        .map(|tn| robOccursCheck(x.clone(), tn.clone()))
        .fold(base, |a, b| a || b)
    }
    match t {
      TypeBinding::TypeVar(y) => x == y,
      TypeBinding::Arrow(args, ret) => check_on_list(&x, &args),
      TypeBinding::Star(t) => robOccursCheck(x, *t),
      TypeBinding::List(t) => robOccursCheck(x, *t),
      TypeBinding::Pair(t1, t2) => robOccursCheck(x.clone(), *t1) || robOccursCheck(x, *t2),
      TypeBinding::Enum(_name, type_vars, constructors) => {
        // TODO filter out nones and apply funciton
        let args: Vec<TypeBinding> = constructors
          .into_iter()
          .map(|(_, a)| a)
          .filter_map(identity)
          .collect();
        check_on_list(&x, &args)
      }
      TypeBinding::TypeConstructorApp(constructor, args) => {
        robOccursCheck(x.clone(), *constructor) || check_on_list(&x, &args)
      }
      _ => false,
    }
  }
  /// Apply type arguments, |args|, to the enum |con|.
  fn apply_type_binding(con: &TypeBinding, args: &Vec<TypeBinding>) -> Result<TypeBinding> {
    // this is a new temperary solution set
    let mut s_set = SolutionSet::new();
    // The constructor must be an enum
    let mut con = con.clone();
    match con {
      TypeBinding::Enum(ref name, ref mut var_args, ref mut _bindings) => {
        // the var_args and args must be the same langth (like funcaion arity)
        if args.len() != var_args.len() {
          return Err(anyhow!(
            "Wrong number of arguments passed to constructor {name}. expected {}, found {}",
            var_args.len(),
            args.len()
          ));
        };
        // get the solution new set for this appllication
        for (var, arg) in zip(var_args, args) {
          s_set.insert(var.clone(), arg.clone());
        }
        // use substitute to apply args
        substitute(&mut con, &s_set);
        return Ok(con);
      }
      _ => Err(anyhow!("{con} is not a type constructor")),
    }
  }
  /// Substitute decided type vars with definitions.
  fn substitute(s: &mut TypeBinding, s_set: &SolutionSet) {
    /// Returns true if substitution was made, false otherwise.
    fn substitute_helper(s: &mut TypeBinding, s_set: &SolutionSet) -> bool {
      match s {
        TypeBinding::TypeVar(x) => {
          if let Some(t) = s_set.get(&x) {
            *s = t.clone();
            true
          } else {
            false
          }
        }
        TypeBinding::Arrow(args, ret) => {
          let mut b = substitute_helper(ret, s_set);
          for mut x in args.iter_mut() {
            b = substitute_helper(&mut x, s_set) || b;
          }
          b
        }
        TypeBinding::Enum(_name, type_vars, bindings) => {
          let mut b = false;
          // if a variable is set remove it from the list and set it in the bindings
          *type_vars = type_vars
            .iter()
            .filter(|var| s_set.get(*var).is_some())
            .cloned()
            .collect();
          //set the variables in the bindings
          for (_name, opt_typ) in bindings.iter_mut() {
            if let Some(ref mut typ) = opt_typ {
              b = substitute_helper(typ, s_set) || b;
            }
          }
          b
        }
        TypeBinding::TypeConstructorApp(constructor, args) => {
          let mut b = substitute_helper(&mut *constructor, s_set);
          for ref mut x in args.iter_mut() {
            b = substitute_helper(x, s_set) || b;
          }
          b
        }
        TypeBinding::Star(t) => substitute_helper(&mut *t, s_set),
        TypeBinding::List(t) => substitute_helper(&mut *t, s_set),
        TypeBinding::Pair(t1, t2) => {
          substitute_helper(&mut *t1, s_set) || substitute_helper(&mut *t2, s_set)
        }
        _ => false,
      }
    }
    // while (s is a variable bound by σ) s := sσ;
    while substitute_helper(s, s_set) {}
  }
  /// unify an equivalent relation
  fn unify_equiv(
    s: &TypeBinding,
    t: &TypeBinding,
    f: &FileLocation,
    s_set: &mut SolutionSet,
    p_set: &mut ProblemSet,
  ) -> Result<()> {
    // while (s is a variable bound by σ) s := sσ;
    let mut s = s.clone();
    substitute(&mut s, &s_set);
    while let TypeBinding::TypeConstructorApp(ref mut con, ref mut args) = s {
      s = apply_type_binding(con, args)?;
    }
    // while (t is a variable bound by σ) t := tσ;
    let mut t = t.clone();
    substitute(&mut t, &s_set);
    while let TypeBinding::TypeConstructorApp(ref mut con, ref mut args) = t {
      t = apply_type_binding(con, args)?;
    }
    if s != t {
      match (s, t) {
        // Type Var checks
        (TypeBinding::TypeVar(x), TypeBinding::TypeVar(y)) => {
          s_set.insert(x, TypeBinding::TypeVar(y));
          Ok(())
        }
        (TypeBinding::TypeVar(x), u) => {
          if robOccursCheck(x.clone(), u.clone()) {
            Err(anyhow!("'{}' Occurs in '{u}'", x.0))
          } else {
            s_set.insert(x, u);
            Ok(())
          }
        }
        (s, TypeBinding::TypeVar(y)) => {
          if robOccursCheck(y.clone(), s.clone()) {
            Err(anyhow!("'{}' Occurs in '{s}'", y.0))
          } else {
            s_set.insert(y, s);
            Ok(())
          }
        }
        // Polymorphic type checks
        (TypeBinding::Arrow(s_args, s_ret), TypeBinding::Arrow(t_args, t_ret)) => {
          // check length
          if s_args.len() != t_args.len() {
            return Err(anyhow!(
              "'{}' and '{}' have different arity",
              TypeBinding::Arrow(s_args, s_ret),
              TypeBinding::Arrow(t_args, t_ret)
            ));
          }

          // check types
          // check args

          for (a, b) in s_args.iter().zip(t_args) {
            p_set.push_back(TypeEquation::Equiv(a.clone(), b, f.clone()));
          }
          // check ret
          p_set.push_back(TypeEquation::Equiv(*s_ret, *t_ret, f.clone()));
          Ok(())
        }

        (TypeBinding::Pair(s1, s2), TypeBinding::Pair(t1, t2)) => {
          p_set.push_back(TypeEquation::Equiv(*s1, *t1, f.clone()));
          p_set.push_back(TypeEquation::Equiv(*s2, *t2, f.clone()));
          Ok(())
        }
        (TypeBinding::List(s1), TypeBinding::List(t1)) => {
          p_set.push_back(TypeEquation::Equiv(*s1, *t1, f.clone()));
          Ok(())
        }
        (TypeBinding::Star(s1), TypeBinding::Star(t1)) => {
          p_set.push_back(TypeEquation::Equiv(*s1, *t1, f.clone()));
          Ok(())
        }
        // test enums
        (
          TypeBinding::Enum(name1, _type_vars1, bindings1),
          TypeBinding::Enum(name2, _type_vars2, bindings2),
        ) => {
          // if the names are not the same, they cant be uified
          if name1 != name2 {
            return Err(anyhow!("{name1} and {name2} are not unifiable"));
          };
          // make shure that the bindings can unify
          for ((_n1, b1o), (_n2, b2o)) in zip(bindings1, bindings2) {
            if let (Some(b1), Some(b2)) = (b1o, b2o) {
              p_set.push_back(TypeEquation::Equiv(b1, b2, f.clone()));
            }
          }
          Ok(())
        }
        // if un-unifieable types
        (s, t) => Err(anyhow!("'{s} == {t}' can't be unified.")),
      }
    } else {
      Ok(())
    }
  }
  /// unify a subtype relation
  fn unify_subtype(
    s: &TypeBinding,
    t: &TypeBinding,
    f: &FileLocation,
    s_set: &mut SolutionSet,
    p_set: &mut ProblemSet,
  ) -> Result<()> {
    // while (s is a variable bound by σ) s := sσ;
    let mut s = s.clone();
    substitute(&mut s, &s_set);

    // while (t is a variable bound by σ) t := tσ;
    let mut t = t.clone();
    substitute(&mut t, &s_set);

    if s != t {
      match (&s, &t) {
        // x<= Any for any type x
        (_, TypeBinding::Any) => Ok(()),

        // Type Var checks
        (TypeBinding::TypeVar(x), TypeBinding::TypeVar(y)) => {
          p_set.push_front(TypeEquation::Or(
            Box::new(TypeEquation::Equiv(s, t.clone(), f.clone())),
            Box::new(TypeEquation::Equiv(t, TypeBinding::Any, f.clone())),
          ));
          Ok(())
        }
        (TypeBinding::TypeVar(x), u) => {
          if u == &TypeBinding::Any {
            Ok(())
          } else if robOccursCheck(x.clone(), u.clone()) {
            Err(anyhow!("'{}' Occurs in '{u}'", x.0))
          } else {
            s_set.insert(x.clone(), u.clone());
            Ok(())
          }
        }
        // TODO double check this one
        (u, TypeBinding::TypeVar(y)) => {
          p_set.push_front(TypeEquation::Or(
            Box::new(TypeEquation::Equiv(s, t.clone(), f.clone())),
            Box::new(TypeEquation::Equiv(t, TypeBinding::Any, f.clone())),
          ));
          Ok(())
        }
        // Polymorphic type checks
        (TypeBinding::Arrow(s_args, s_ret), TypeBinding::Arrow(t_args, t_ret)) => {
          // check length
          if s_args.len() != t_args.len() {
            // -> s1 ... sn <= t1 ... tn+1
            // iff s1 <= t1 ... sn-1 <= tn-1 and tn is a star type
            if s_args.len() == t_args.len() + 1
              && t_args.last().map(|x| x.is_star()).unwrap_or(false)
            {
            } else {
              return Err(anyhow!("'{s}' and '{t}' have different arity"));
            }
          }

          // check types
          // check args
          for (a, b) in s_args.iter().zip(t_args) {
            p_set.push_back(TypeEquation::Equiv(a.clone(), b.clone(), f.clone()));
          }
          // check ret
          p_set.push_back(TypeEquation::Equiv(
            *s_ret.clone(),
            *t_ret.clone(),
            f.clone(),
          ));
          Ok(())
        }

        (TypeBinding::Pair(s1, s2), TypeBinding::Pair(t1, t2)) => {
          p_set.push_back(TypeEquation::SubType(*s1.clone(), *t1.clone(), f.clone()));
          p_set.push_back(TypeEquation::SubType(*s2.clone(), *t2.clone(), f.clone()));
          Ok(())
        }
        (TypeBinding::List(s1), TypeBinding::List(t1)) => {
          p_set.push_back(TypeEquation::SubType(*s1.clone(), *t1.clone(), f.clone()));
          Ok(())
        }

        (TypeBinding::Star(s1), TypeBinding::Star(t1)) => {
          p_set.push_back(TypeEquation::SubType(*s1.clone(), *t1.clone(), f.clone()));
          Ok(())
        }
        // if un-unifieable types
        (s, t) => Err(anyhow!("'{s} ⊑ {t}'can't be unified.")),
      }
    } else {
      Ok(())
    }
  }

  /// Unify a single equation |e|
  fn unify_equation(
    e: TypeEquation,
    s_set: &mut SolutionSet,
    p_set: &mut ProblemSet,
  ) -> Result<(), MyError> {
    match e {
      TypeEquation::Equiv(s, t, f) => to_myerror(unify_equiv(&s, &t, &f, s_set, p_set), &f),
      TypeEquation::SubType(s, t, f) => to_myerror(unify_subtype(&s, &t, &f, s_set, p_set), &f),
      TypeEquation::Or(e1, e2) => {
        unify_equation(*e1, s_set, p_set).or_else(|_| unify_equation(*e2, s_set, p_set))
      }
    }
  }

  let mut s_set = SolutionSet::new();

  while let Some(p) = p_set.pop_back() {
    unify_equation(p, &mut s_set, p_set)?
  }
  return Ok(s_set);
}

/// check the types and fill in the important type bindings where the user did not write them
pub fn type_check(
  input: &mut AST,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<TypeBinding, MyError> {
  match input {
    AST::Fun(ref mut f, loc) => to_myerror(type_of_function(f, loc, context, problem_set), &loc),
    AST::Val(ref mut val, loc) => to_myerror(type_of_value(val, &loc, context, problem_set), &loc),
    AST::Var(name, loc) => context
      .lookup(name.clone())
      .ok_or(TypeError::NoVar(name.clone()).into_myerror(loc)),
    AST::Let(ref mut bindings, ref mut body, loc) => {
      let mut new_context = context.new_scope();
      apply_bindings(bindings, loc, &mut new_context, problem_set)?;
      // the let expression returns the last thing in the body
      body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
        type_check(ast, &mut new_context, problem_set)
      })
    }
    AST::LetRec(ref mut bindings, ref mut body, loc) => {
      let mut new_context = context.new_scope();
      // All of the bindeings should be functions that declare there return type
      apply_letrec_bindings(bindings, loc, &mut new_context, problem_set)?;
      // type check the body
      body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
        type_check(ast, &mut new_context, problem_set)
      })
    }
    AST::Enum(name, bindings, loc) => {
      add_enum_funcs_to_context(&name, &bindings, &vec![], &loc, context, problem_set)?;
      Ok(TypeBinding::Unit)
    }
    AST::Match(ref mut argument, ref mut conditions, loc) => {
      let arg_typ = type_check(argument, context, problem_set)?;
      match_check_conditions(&arg_typ, conditions, &loc, context, problem_set)
    }
    AST::Define(ref mut binding, loc) => {
      apply_binding(binding, loc.clone(), context, problem_set)?;
      // can use unwrap here because apply binding enuses it will be Some(_)
      Ok(binding.1.clone().unwrap())
    }
    AST::Set(name, ref mut val, loc) => {
      let b_typ = type_check(val, context, problem_set)?;
      let typ = context
        .lookup(name.to_string())
        .ok_or(TypeError::NoVar(name.to_string()).into_myerror(loc))?;
      // make shure the types match
      // b_typ <= typ
      problem_set.push_back(TypeEquation::SubType(b_typ, typ.clone(), loc.clone()));
      // if !typ.same_as(b_typ.clone(), &context) {
      //   return Err(TypeError::Mismatch(name.clone(), typ, b_typ).into_myerror(loc));
      // }
      // set returns the value set
      return Ok(typ);
    }
    AST::Sexpr(ref mut asts, loc) => {
      // check that the expession is not empy
      if asts.len() < 1 {
        return Err(TypeError::EmpySEpr.into_myerror(loc));
      }
      //
      // get the type of the function
      // use a new type var scope to avoid bogus ocours check errors
      match type_check(&mut asts[0], context, problem_set)?.new_type_var_scope() {
        TypeBinding::Arrow(a_args, a_ret) => {
          let b_args = asts[1..]
            .iter_mut()
            .map(|ast: &mut AST| type_check(ast, context, problem_set))
            .collect::<Result<Vec<TypeBinding>, MyError>>()?;
          function_application_check(&a_args, &b_args, loc.clone(), context, problem_set)
            .map_err(|e| e.into_myerror(loc))?;
          Ok(*a_ret.clone())
        }
        x => return Err(TypeError::CallOfNonFunc(x).into_myerror(loc)),
      }
    }
  }
}

/// Type checks a match statment
fn match_check_conditions(
  arg_typ: &TypeBinding,
  conditions: &mut Vec<(MatchCondition, Vec<AST>)>,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<TypeBinding, MyError> {
  fn lookup_implementation(
    name: &str,
    impls: &Vec<(String, Option<TypeBinding>)>,
  ) -> Option<Option<TypeBinding>> {
    for (impl_name, opt_typ) in impls.into_iter() {
      if name == impl_name {
        return Some(opt_typ.clone());
      }
    }
    None
  }
  // Rule : arg_type must be an Enum type
  todo!("handel type variables for enums if needed");
  let (enum_name, impls) = match arg_typ {
    TypeBinding::Enum(name, _typ_vars, impls) => (name, impls),
    _ => {
      return Err(
        TypeError::Other(anyhow!("Type of match argument must be an Enum/Sum type"))
          .into_myerror(loc),
      )
    }
  };
  // set of used implimentations
  let mut used_impls: HashSet<String> = HashSet::new();
  // set of types returned
  let mut return_typs: Vec<TypeBinding> = vec![];
  let mut default_exists = false;
  for (condition, body) in conditions.iter_mut() {
    // Rule 1: All Match Conditions must match there implantations
    match condition {
      MatchCondition::Const(cond_name, ref mut c_body) => {
        if let Some(found_typ) = lookup_implementation(cond_name, impls) {
          used_impls.insert(cond_name.clone());
          if let Some(ref mut c_body) = c_body {
            let c_typ = type_check(c_body, context, problem_set)?;
            if found_typ == None {
              return Err(
                TypeError::Other(anyhow!(
                  "A match condition must have the same araty as the implementation it references"
                ))
                .into_myerror(loc),
              );
            } else {
              problem_set.push_back(TypeEquation::Equiv(
                found_typ.unwrap(),
                c_typ,
                c_body.position(),
              ));
            }
          } else {
            if found_typ != None {
              return Err(
                TypeError::Other(anyhow!(
                  "A match condition must have the same araty as the implementation it references"
                ))
                .into_myerror(loc),
              );
            }
          }
          // record the type returned by the body
          let mut new_context = context.new_scope();
          let body_typ: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
            type_check(&mut *ast, &mut new_context, problem_set)
          })?;
          return_typs.push(body_typ);
        } else {
          return Err(
            TypeError::Other(anyhow!(
              "{enum_name} does not have an implimentation named {cond_name}"
            ))
            .into_myerror(loc),
          );
        }
      }
      MatchCondition::SingleV(cond_name, var_name) => {
        if let Some(found_typ) = lookup_implementation(cond_name, impls) {
          if let Some(found_typ) = found_typ {
            // list found implantation
            used_impls.insert(cond_name.clone());
            // new context with bound variables
            let mut new_context = context.new_scope();
            to_myerror(new_context.declare(var_name.to_string(), found_typ), loc)?;
            // record the type returned by the body
            let body_typ: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
              type_check(&mut *ast, &mut new_context, problem_set)
            })?;

            return_typs.push(body_typ);
          } else {
            return Err(
              TypeError::Other(anyhow!(
                "{enum_name} does not have an implimentation named {cond_name} with desired arity"
              ))
              .into_myerror(loc),
            );
          }
        } else {
          return Err(
            TypeError::Other(anyhow!(
              "{enum_name} does not have an implimentation named {cond_name}"
            ))
            .into_myerror(loc),
          );
        }
      }
      MatchCondition::Default => {
        // seen a default condition
        default_exists = true;
        // record the type returned by the body
        let mut new_context = context.new_scope();
        let body_typ: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
          type_check(&mut *ast, &mut new_context, problem_set)
        })?;
        return_typs.push(body_typ);
      }
    }
  }

  // Rule 2: If there is no default condition, then the match conditions must cover all implantations.
  if default_exists == false {
    // find all implantations. Garented to be non-empty because all enums must have at least 1 implantation
    let all_impls: HashSet<String> = impls
      .into_iter()
      .map(|(name, _type)| name.to_string())
      .collect();
    //list of uncoverd match conditions
    let un_implemented: HashSet<String> = all_impls
      .difference(&used_impls)
      .map(|x| x.clone())
      .collect();
    if !un_implemented.is_empty() {
      let mut requierd_impls = un_implemented.iter();
      let mut un_implemented_str = "".to_owned();
      for i in requierd_impls {
        un_implemented_str.push_str(format!("{i}, ").as_str());
      }

      return Err(
        TypeError::Other(anyhow!("uncovered implementations: {un_implemented_str}"))
          .into_myerror(loc),
      );
    }
  }

  // Rule 3: all bodies must return the same type (TODO allow subtypes)

  // garented to not panik because if there is nothing in return_typs
  // then we throw an error for not haveing a default.
  let mut pre_typ = return_typs.pop().unwrap();
  for typ in return_typs {
    // works because if a=b and b=c then a=c.
    problem_set.push_back(TypeEquation::Equiv(
      pre_typ.clone(),
      typ.clone(),
      loc.clone(),
    ));
    pre_typ = typ;
  }
  return Ok(pre_typ);
}

/// Adds enum implimentations as functions to the context.
/// also adds a type deffinition for the name
fn add_enum_funcs_to_context(
  enum_name: &str,
  bindings: &Vec<(String, Option<TypeBinding>)>,
  declared_type_vars: &Vec<(String, u64)>,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<(), MyError> {
  // Rule 1: all enums must have at least 1 function that implantation them
  if bindings.is_empty() {
    return Err(
      TypeError::Other(anyhow!("Enum must have at least 1 implantation")).into_myerror(loc),
    );
  }
  // check that the only typeVars used in the functions are ones that are declared
  let type_vars: HashSet<(String, u64)> = declared_type_vars.into_iter().cloned().collect();
  for (_name, opt_arg) in bindings {
    if let Some(arg) = opt_arg {
      // if arg uses undeclared type variables
      if !arg.get_type_vars().is_subset(&type_vars) {
        let vars: String = arg
          .get_type_vars()
          .difference(&type_vars)
          .map(|(name, _num)| name.clone())
          .collect::<Vec<String>>()
          .join(", ");
        return Err(
      TypeError::Other(anyhow!("Use of undeclared type variables ({vars}), please declare them right after the Enum name")).into_myerror(loc),
    );
      }
    }
  }

  let enum_type = Box::new(TypeBinding::Enum(
    enum_name.to_string(),
    declared_type_vars.clone(),
    bindings.clone(),
  ));
  // add type to type deffinitions
  context.define_type(enum_name.to_string(), (*enum_type).clone());
  let mut names = vec![];
  for (name, opt_typ) in bindings {
    // Rule 2: All implantations of the enum must have different names
    if names.contains(name) {
      return Err(TypeError::Other(anyhow!("Enum must not repeat names")).into_myerror(loc));
    }
    names.push(name.clone());
    // Add implimentation to context
    let new_typ = TypeBinding::Arrow(opt_typ.clone().into_iter().collect(), enum_type.clone());
    let r = context.declare(name.to_string(), new_typ);
    if let Err(e) = r {
      return Err(TypeError::Other(e).into_myerror(loc));
    };
  }

  Ok(())
}

/// check if function application args type check
/// Also checks if there is a Star type, that it is at the end
/// |a_args|: the arguments the function needs to be applied
/// |b_args|: the arguments trying to be applied to the function
fn function_application_check(
  a_args: &[TypeBinding],
  b_args: &[TypeBinding],
  loc: FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
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
      return Err(anyhow!("Star types must come at the end of arguments.").into());
    }

    // b_args is verrified not to be empty
    let b = b_args.pop().unwrap();
    // destar a if nessesary
    let a = match &a {
      Some(TypeBinding::Star(x)) => Some(*x.clone()),
      _ => a.clone(),
    };
    // verrify that b can be coerced to a.
    // b <= a
    problem_set.push_back(TypeEquation::SubType(b, a.clone().unwrap(), loc.clone()));
  }
  // If a_args has more elemets, it should only be one Star type
  if (a_args.len() == 1 && !a_args[0].is_star()) || a_args.len() > 1 {
    return Err(anyhow!("Applied wrong number of args").into());
  }
  Ok(())
}

/// apply one binding, and set the type of the binding to Some(_) if it was None.
fn apply_binding(
  bind: &mut Binding,
  loc: FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<(), MyError> {
  let (name, ref mut typ, ref mut body) = bind;
  // type of the body
  let b_typ = type_check(body, context, problem_set)?;
  // set type if it does not exist
  if typ.is_none() {
    *typ = Some(b_typ.clone());
  } else {
    // if it does, make shure it matches
    // b_typ <= typ
    problem_set.push_back(TypeEquation::SubType(
      b_typ.clone(),
      typ.clone().unwrap(),
      loc,
    ));
  }
  // If it passes, add it to the context
  to_myerror(context.declare(name.to_owned(), b_typ), &body.position())?;
  Ok(())
}

/// Add all bindings to context, then check there bodies.
/// all bindings must be functions that declare there return type.
fn apply_letrec_bindings(
  bindings: &mut Vec<Binding>,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<(), MyError> {
  // add binding to context
  for (name, typ, body) in &mut *bindings {
    if let Some(typ) = typ {
      if !typ.is_function() {
        return Err(TypeError::LetRecFail.into_myerror(loc));
      } else {
        to_myerror(
          context.declare(name.to_owned(), typ.clone()),
          &body.position(),
        )?;
      }
    } else {
      return Err(TypeError::LetRecFail.into_myerror(loc));
    }
  }
  // type check each binding's body
  for (name, typ, body) in &mut *bindings {
    // type of the body
    let b_typ = type_check(body, context, problem_set)?;
    // set type if it does not exist
    if typ.is_none() {
      *typ = Some(b_typ.clone());
    } else {
      // if it does, make shure it matches
      // b_typ <= typ
      problem_set.push_back(TypeEquation::SubType(
        b_typ.clone(),
        typ.clone().unwrap(),
        loc.clone(),
      ));
    }
  }
  Ok(())
}

/// Apply bindings
fn apply_bindings(
  bindings: &mut Vec<Binding>,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<(), MyError> {
  for mut bind in bindings {
    apply_binding(&mut bind, loc.clone(), context, problem_set)?;
  }
  Ok(())
}

/// Find the type of values
/// TODO: finish when type system can suport more
fn type_of_value(
  val: &mut Value,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<TypeBinding> {
  let typ = match val {
    Value::EnumVal(_, _) => {
      // This should never happen because Enum values are parsed as functions first
      return Err(anyhow!("Found written EnumVal, Should not happen"));
    }
    Value::Char(_) => TypeBinding::Char,
    Value::Int(_) => TypeBinding::Int,
    Value::Str(_) => TypeBinding::Str,
    Value::Bool(_) => TypeBinding::Bool,
    Value::Unit => TypeBinding::Unit,
    Value::Fun(ref mut f, _) => type_of_function(f, loc, context, problem_set)?,
    Value::Meval(v, _) => type_check(&mut *v, context, problem_set)?,
    Value::Pair(a, b) => TypeBinding::Pair(
      Box::new(type_of_value(&mut *a, loc, context, problem_set)?),
      Box::new(type_of_value(&mut *b, loc, context, problem_set)?),
    ),
    Value::List(vs) => {
      if vs.len() == 0 {
        TypeBinding::TypeVar(("_".to_string(), get_new_typevar_scope()))
      } else {
        let lst_typ = type_of_value(&mut vs[0], loc, context, problem_set)?;
        for mut v in vs {
          let v_typ = type_of_value(&mut v, loc, context, problem_set)?;
          problem_set.push_back(TypeEquation::Equiv(lst_typ.clone(), v_typ, loc.clone()));
        }
        lst_typ
      }
    }
  };
  Ok(typ)
}
/// Returns the type of a function
fn type_of_function(
  f: &mut LFunction,
  loc: &FileLocation,
  context: &mut Context,
  problem_set: &mut ProblemSet,
) -> Result<TypeBinding> {
  match f {
    LFunction::EnumConstructor(_constructor_name, _typ) => {
      // THis should not be called because this kind of function only exists
      // durring runtime. During parseing and type checking, it is seen as a
      // normal function

      Err(anyhow!("Found written EnumConstructor, Should not happen"))
    }
    LFunction::BuiltinF(name, _) | LFunction::BuiltinM(name, _) => {
      Ok(context.lookup(name.to_string()).unwrap())
    }
    LFunction::LambdaF(args, ret, body) | LFunction::LambdaL(args, ret, body) => {
      // list of arg types in arrow type
      let mut types = vec![];
      let mut new_context = context.new_scope();
      //add variable to context
      for (name, typ) in args {
        types.append(&mut vec![typ.clone()]);
        new_context.declare(name.to_string(), typ.to_owned())?;
      }
      // get the return type of the function
      if let Some(ret) = ret {
        let found: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
          type_check(&mut *ast, &mut new_context, problem_set)
        })?;
        problem_set.push_back(TypeEquation::Equiv(ret.clone(), found, loc.clone()));
        Ok(TypeBinding::Arrow(types, Box::new(ret.clone())))
      } else {
        let ret: TypeBinding = body.iter_mut().try_fold(TypeBinding::Unit, |_, ast| {
          type_check(&mut *ast, &mut new_context, problem_set)
        })?;
        Ok(TypeBinding::Arrow(types, Box::new(ret)))
      }
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
      TypeError::LetRecFail => {
        "A Binding in a letrec expression must be a function with a written type".to_owned()
      }
    };

    MyError::new(ErrorKind::TypeCheck(message), loc.to_owned())
  }
}

// TESTS

#[cfg(test)]
mod test {
  use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
  };

  use super::{type_unification, FileLocation, ProblemSet};

  #[test]
  fn test_unification_simple() {
    use super::{ProblemSet, SolutionSet, TypeBinding, TypeEquation};
    /// Test that a found solution and a true solution are the same.
    /// drops the number part of type variables.
    /// returns true if solutions are equal.
    fn test_solution(
      found_solution: HashMap<(String, u64), TypeBinding>,
      true_solution: HashMap<String, TypeBinding>,
    ) -> bool {
      let mut ret = found_solution.len() == true_solution.len();
      for ((k, _), v) in found_solution.into_iter() {
        ret = ret && (true_solution.get(&k).unwrap() == &v);
      }
      ret
    }

    // test1
    fn test1() {
      let mut problem: ProblemSet = {
        let mut x = ProblemSet::new();
        x.push_back(TypeEquation::Equiv(
          TypeBinding::from_str("(Pair x Int)").unwrap(),
          TypeBinding::from_str("( Pair Unit y)").unwrap(),
          FileLocation::empty(),
        ));
        x
      };
      let sol = type_unification(&mut problem);
      let solution = {
        let mut x = HashMap::new();
        x.insert("x".to_owned(), TypeBinding::Unit);
        x.insert("y".to_owned(), TypeBinding::Int);
        x
      };
      assert!(sol.is_ok());
      assert!(test_solution(sol.unwrap(), solution));
    }
    fn test2() {
      let mut problem: ProblemSet = {
        let mut x = ProblemSet::new();
        let x_var = TypeBinding::TypeVar(("x".to_owned(), 1));
        x.push_back(TypeEquation::Equiv(
          x_var.clone(),
          TypeBinding::List(Box::new(x_var)),
          FileLocation::empty(),
        ));
        x
      };
      let sol = type_unification(&mut problem);
      assert!(sol.is_err());
    }
    // test3
    fn test3() {
      let mut problem: ProblemSet = {
        let mut x = ProblemSet::new();
        let x_var = TypeBinding::TypeVar(("x".to_owned(), 0));
        let y_var = TypeBinding::TypeVar(("y".to_owned(), 0));
        x.push_back(TypeEquation::SubType(
          x_var.clone(),
          y_var.clone(),
          FileLocation::empty(),
        ));
        x.push_back(TypeEquation::SubType(
          y_var.clone(),
          x_var.clone(),
          FileLocation::empty(),
        ));
        x.push_back(TypeEquation::Equiv(
          y_var.clone(),
          TypeBinding::Int,
          FileLocation::empty(),
        ));
        x
      };
      let sol = type_unification(&mut problem);
      let solution = {
        let mut x = HashMap::new();
        x.insert("x".to_owned(), TypeBinding::Int);
        x.insert("y".to_owned(), TypeBinding::Int);
        x
      };
      assert!(sol.is_ok());
      assert!(test_solution(sol.unwrap(), solution));
    }
    // test4
    fn test4() {
      let mut problem: ProblemSet = {
        let mut x = ProblemSet::new();
        let x_var = TypeBinding::TypeVar(("x".to_owned(), 0));
        let y_var = TypeBinding::TypeVar(("y".to_owned(), 0));
        x.push_back(TypeEquation::SubType(
          x_var.clone(),
          y_var.clone(),
          FileLocation::empty(),
        ));
        x.push_back(TypeEquation::SubType(
          y_var.clone(),
          x_var.clone(),
          FileLocation::empty(),
        ));
        x.push_back(TypeEquation::Equiv(
          y_var.clone(),
          TypeBinding::Int,
          FileLocation::empty(),
        ));
        x.push_back(TypeEquation::Equiv(
          x_var.clone(),
          TypeBinding::Unit,
          FileLocation::empty(),
        ));
        x
      };
      let sol = type_unification(&mut problem);
      assert!(sol.is_err());
    }

    test1();
    test2();
    test3();
    test4();
  }

  #[test]
  fn test_function_application() {
    use super::{function_application_check, Context, TypeBinding::*};
    // test1
    let test1 = vec![Int, Int, Str, Star(Box::new(Bool))];
    // test1.1
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_ok());
    // test1.2
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_ok());
    // test1.3
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool, Bool, Bool],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_ok());
    assert!(function_application_check(
      &test1.clone(),
      &vec![Int, Int, Str, Bool],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_ok());
    // test 2
    let test2 = vec![Star(Box::new(Str)), Char];
    // test 2.1
    assert!(function_application_check(
      &test2,
      &vec![Str, Char],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_err(),);
    assert!(function_application_check(
      &test2,
      &vec![Char, Int],
      FileLocation::empty(),
      &mut Context::default(),
      &mut ProblemSet::new()
    )
    .is_err());
  }
}
