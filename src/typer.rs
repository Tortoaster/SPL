use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use error::Result;

use crate::lexer::{Lexable, Field};
use crate::parser::error::ParseError;
use crate::parser::Parsable;
use crate::tree::{Decl, Exp, FunCall, FunDecl, FunType, Id, SPL, Stmt, VarDecl};
use crate::typer::error::TypeError;

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable(usize);

impl TypeVariable {
    fn bind(&self, to: &Type) -> Result<Substitution> {
        if let Type::Polymorphic(v) = to {
            if *self == *v {
                return Ok(Substitution::new());
            }
        }

        if to.free_vars().contains(self) {
            return Err(TypeError::Recursive(self.clone(), to.clone()));
        }

        let mut s = Substitution::new();
        s.insert(self.clone(), to.clone());
        Ok(s)
    }
}

pub struct Generator {
    current: usize
}

impl Generator {
    pub fn new() -> Self {
        Generator {
            current: 0
        }
    }

    pub fn fresh(&mut self) -> TypeVariable {
        self.current += 1;
        TypeVariable(self.current)
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Type {
    Void,
    Int,
    Bool,
    Char,
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Function(Box<Type>, Box<Type>),
    Polymorphic(TypeVariable),
}

impl Type {
    /// Returns a type into a vector of the argument types and the return type
    fn unfold(&self) -> Vec<Self> {
        match self {
            Type::Function(a, b) => {
                let mut vec = vec![a.as_ref().clone()];
                vec.append(&mut b.unfold());
                vec
            }
            _ => vec![self.clone()]
        }
    }

    fn format(&self, poly_names: &HashMap<TypeVariable, char>) -> String {
        match self {
            Type::Void => format!("Void"),
            Type::Int => format!("Int"),
            Type::Bool => format!("Bool"),
            Type::Char => format!("Char"),
            Type::Tuple(l, r) => format!("({}, {})", l.format(poly_names), r.format(poly_names)),
            Type::Array(a) => format!("[{}]", a.format(poly_names)),
            Type::Function(a, b) => format!("({} -> {})", a.format(poly_names), b.format(poly_names)),
            Type::Polymorphic(v) => format!("{}", poly_names.get(&v).unwrap_or(&'?'))
        }
    }
}

trait Union {
    fn unify_with(&self, other: &Self) -> Result<Substitution>;
}

impl Union for Type {
    fn unify_with(&self, other: &Self) -> Result<Substitution> {
        match (self, other) {
            (Type::Void, Type::Void) | (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Char, Type::Char) => Ok(Substitution::new()),
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => {
                let subst_l = l1.unify_with(l2)?;
                let subst_r = r1.apply(&subst_l).unify_with(&r2.apply(&subst_l))?;
                Ok(subst_r.compose(&subst_l))
            }
            (Type::Array(t1), Type::Array(t2)) => t1.unify_with(t2),
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                let subst_a = a1.unify_with(a2)?;
                let subst_b = b1.apply(&subst_a).unify_with(&b2.apply(&subst_a))?;
                Ok(subst_b.compose(&subst_a))
            }
            (Type::Polymorphic(v), t) | (t, Type::Polymorphic(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Mismatch { expected: t1.clone(), found: t2.clone() })
        }
    }
}

impl Union for Option<Type> {
    fn unify_with(&self, other: &Self) -> Result<Substitution> {
        if let (Some(t1), Some(t2)) = (self, other) {
            t1.unify_with(&t2)
        } else {
            Ok(Substitution::new())
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct PolyType {
    pub variables: Vec<TypeVariable>,
    pub inner: Type,
}

impl PolyType {
    pub fn instantiate(&self, gen: &mut Generator) -> Type {
        let fresh = std::iter::repeat_with(|| Type::Polymorphic(gen.fresh()));
        let subst = Substitution(self.variables.iter().cloned().zip(fresh).collect());
        self.inner.apply(&subst)
    }
}

impl From<Type> for PolyType {
    fn from(inner: Type) -> Self {
        PolyType {
            variables: vec![],
            inner,
        }
    }
}

impl FromStr for PolyType {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let fun_type = FunType::parse(&mut s.tokenize().unwrap().peekable())?;

        let mut gen = Generator::new();
        let mut poly_names: HashMap<Id, TypeVariable> = HashMap::new();

        let arg_types: Vec<Type> = fun_type.arg_types
            .iter()
            .map(|t| t.transform(&mut gen, &mut poly_names))
            .collect();

        let ret_type = fun_type.ret_type.transform(&mut gen, &mut poly_names);

        let t = arg_types.into_iter().rfold(ret_type, |ret, arg| Type::Function(Box::new(arg), Box::new(ret)));
        Ok(PolyType { variables: poly_names.values().cloned().collect(), inner: t })
    }
}

impl fmt::Display for PolyType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let poly_names: HashMap<TypeVariable, char> = self
            .free_vars()
            .into_iter()
            .zip('a'..'z')
            .collect();
        write!(f, "{}", self.inner.format(&poly_names))
    }
}

#[derive(Clone, Debug)]
pub struct Environment(HashMap<Id, PolyType>);

impl Environment {
    pub fn new(gen: &mut Generator) -> Self {
        let mut env = Environment(HashMap::new());
        for (name, annotation) in vec![
            ("print", "a -> Void"),
            ("isEmpty", "[a] -> Bool"),
            ("hd", "[a] -> a"),
            ("tl", "[a] -> [a]"),
            ("fst", "(a, b) -> a"),
            ("snd", "(a, b) -> b"),
            ("not", "Bool -> Bool"),
            ("add", "Int Int -> Int"),
            ("sub", "Int Int -> Int"),
            ("mul", "Int Int -> Int"),
            ("div", "Int Int -> Int"),
            ("mod", "Int Int -> Int"),
            ("eq", "a a -> Bool"),
            ("ne", "a a -> Bool"),
            ("lt", "Int Int -> Bool"),
            ("gt", "Int Int -> Bool"),
            ("le", "Int Int -> Bool"),
            ("ge", "Int Int -> Bool"),
            ("and", "Bool Bool -> Bool"),
            ("or", "Bool Bool -> Bool"),
            ("cons", "a [a] -> [a]"),
        ] {
            let mut t: PolyType = annotation.parse().unwrap();
            t = env.generalize(&t.instantiate(gen));
            env.insert(Id(name.to_owned()), t);
        }
        env
    }

    pub fn generalize(&self, instance: &Type) -> PolyType {
        PolyType {
            variables: instance
                .free_vars()
                .difference(&self.free_vars())
                .cloned()
                .collect(),
            inner: instance.clone(),
        }
    }
}

impl Deref for Environment {
    type Target = HashMap<Id, PolyType>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Environment {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Eq, PartialEq, Debug)]
pub struct Substitution(HashMap<TypeVariable, Type>);

impl Substitution {
    fn new() -> Self {
        Substitution(HashMap::new())
    }

    fn compose(&self, other: &Self) -> Self {
        other
            .iter()
            .map(|(k, v)| (*k, v.apply(&self)))
            .chain(self
                .iter()
                .map(|(k, v)| (k.clone(), v.clone()))
            )
            .collect()
    }
}

impl Deref for Substitution {
    type Target = HashMap<TypeVariable, Type>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Substitution {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromIterator<(TypeVariable, Type)> for Substitution {
    fn from_iter<T: IntoIterator<Item=(TypeVariable, Type)>>(iter: T) -> Self {
        Substitution(iter.into_iter().collect())
    }
}

pub trait Typed {
    fn free_vars(&self) -> HashSet<TypeVariable>;

    fn apply(&self, subst: &Substitution) -> Self;
}

impl Typed for Type {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        match self {
            Type::Void | Type::Int | Type::Bool | Type::Char => HashSet::new(),
            Type::Tuple(l, r) => l
                .free_vars()
                .union(&r.free_vars())
                .cloned()
                .collect(),
            Type::Array(a) => a.free_vars(),
            Type::Function(a, b) => a
                .free_vars()
                .union(&b.free_vars())
                .cloned()
                .collect(),
            Type::Polymorphic(v) => Some(*v).into_iter().collect(),
        }
    }

    fn apply(&self, subst: &Substitution) -> Self {
        match self {
            Type::Void | Type::Int | Type::Bool | Type::Char => self.clone(),
            Type::Tuple(l, r) => Type::Tuple(Box::new(l.apply(subst)), Box::new(r.apply(subst))),
            Type::Array(a) => Type::Array(Box::new(a.apply(subst))),
            Type::Function(a, b) => Type::Function(Box::new(a.apply(subst)), Box::new(b.apply(subst))),
            Type::Polymorphic(v) => subst.get(v).unwrap_or(self).clone(),
        }
    }
}

impl<T: Typed> Typed for Vec<T> {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self
            .iter()
            .flat_map(|t| t.free_vars())
            .collect()
    }

    fn apply(&self, subst: &Substitution) -> Self {
        self
            .iter()
            .map(|t| t.apply(&subst))
            .collect()
    }
}

impl Typed for PolyType {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self.inner
            .free_vars()
            .difference(&self.variables.iter().cloned().collect())
            .cloned()
            .collect()
    }

    fn apply(&self, subst: &Substitution) -> Self {
        PolyType {
            variables: self.variables.clone(),
            inner: self.inner
                .apply(&Substitution(subst
                    .iter()
                    .filter(|&(t, _)| !self.variables.contains(t))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect())),
        }
    }
}

impl Typed for Environment {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self
            .values()
            .flat_map(|t| t.free_vars())
            .collect()
    }

    fn apply(&self, subst: &Substitution) -> Self {
        Environment(self.iter().map(|(k, v)| (k.clone(), v.apply(subst))).collect())
    }
}

pub trait Infer {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)>;
}

pub trait InferMut {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type>;
}

pub trait TryInfer {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<Type>)>;
}

impl InferMut for SPL {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        // Add global variables and functions to scope
        self.decls.iter()
            .map(|decl| match decl {
                Decl::VarDecl(decl) => {
                    if env.insert(decl.id.clone(), decl.var_type.transform(gen).into()).is_some() {
                        Err(TypeError::Conflict(decl.id.clone()))
                    } else {
                        Ok(())
                    }
                }
                Decl::FunDecl(decl) => {
                    let mut poly_names: HashMap<Id, TypeVariable> = HashMap::new();
                    let (arg_annotations, ret_annotation) = match &decl.fun_type {
                        None => {
                            let args: Vec<Type> = std::iter::repeat_with(|| Type::Polymorphic(gen.fresh()))
                                .take(decl.args.len())
                                .collect();
                            (args, Type::Polymorphic(gen.fresh()))
                        }
                        Some(fun_type) => {
                            let args: Vec<Type> = fun_type.arg_types
                                .iter()
                                .map(|t| t.transform(gen, &mut poly_names))
                                .collect();
                            (args, fun_type.ret_type.transform(gen, &mut poly_names))
                        }
                    };
                    let inner = arg_annotations
                        .into_iter()
                        .rfold(ret_annotation, |t, annotation| Type::Function(Box::new(annotation), Box::new(t)));
                    if env.insert(decl.id.clone(), inner.into()).is_some() {
                        Err(TypeError::Conflict(decl.id.clone()))
                    } else {
                        Ok(())
                    }
                }
            }).collect::<Result<()>>()?;

        // Infer types of inner declarations
        self.decls
            .iter()
            .map(|decl| decl.infer_type_mut(env, gen))
            .collect::<Result<Vec<Type>>>()?;

        Ok(Type::Void)
    }
}

impl InferMut for Decl {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer_type_mut(env, gen),
            Decl::FunDecl(fun_decl) => fun_decl.infer_type_mut(env, gen)
        }
    }
}

impl InferMut for VarDecl {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        let (subst_i, inferred) = self.exp.infer_type(env, gen)?;
        let subst_u = inferred.unify_with(&self.var_type.transform(gen))?;
        let t = PolyType { variables: vec![], inner: inferred.apply(&subst_u.compose(&subst_i)) };
        env.insert(self.id.clone(), t);
        Ok(Type::Void)
    }
}

impl InferMut for FunDecl {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        // TODO: check for doubly defined variables in functions
        // TODO: namespace for functions and variables
        // Create local scope
        let mut local = env.clone();
        let mut arg_types = local
            .get(&self.id)
            .ok_or(TypeError::Unbound(self.id.clone()))?.inner
            .unfold();
        let ret_type = arg_types.pop().unwrap();

        // Add arguments to local scope
        local.extend(self.args
            .iter()
            .cloned()
            .zip(arg_types
                .into_iter()
                .map(|arg| arg.into())));

        // Add variable declarations to local scope
        self.var_decls
            .iter()
            .map(|decl| decl.infer_type_mut(&mut local, gen))
            .collect::<Result<Vec<Type>>>()?;

        // Infer types in inner statements
        let (subst_i, inferred) = self.stmts.try_infer_type(&local, gen)?;

        // Check return type
        let subst_r = ret_type.unify_with(&inferred.unwrap_or(Type::Void))?;

        *env = env.apply(&subst_r.compose(&subst_i));
        Ok(Type::Void)
    }
}

impl TryInfer for Vec<Stmt> {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<Type>)> {
        let mut env = env.clone();
        let mut current = None;

        let subst = self
            .iter()
            .fold(Ok(Substitution::new()), |acc, stmt| {
                let subst_a = acc?;

                let (subst_i, inferred) = stmt.try_infer_type(&env, gen)?;

                let subst_u = current.unify_with(&inferred)?;

                let subst = subst_u.compose(&subst_i.compose(&subst_a));
                env = env.apply(&subst);

                if inferred.is_some() && current.is_none() {
                    current = inferred;
                }

                if let Some(t) = &current {
                    current = Some(t.apply(&subst));
                }

                Ok(subst)
            })?;

        Ok((subst, current))
    }
}

impl TryInfer for Stmt {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<Type>)> {
        match self {
            Stmt::If(c, t, e) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer_type(env, gen)?;
                let env = &env.apply(&subst_t);

                let (subst_e, ret_e) = e.try_infer_type(env, gen)?;

                let subst_r = ret_e.unify_with(&ret_t)?;

                let subst = subst_r.compose(&subst_e.compose(&subst_t.compose(&subst)));
                let ret_type = if let (Some(_), Some(t)) = (ret_t, ret_e) {
                    Some(t.apply(&subst))
                } else {
                    None
                };

                Ok((subst, ret_type))
            }
            Stmt::While(c, t) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer_type(env, gen)?;

                let subst = subst_t.compose(&subst);
                let ret_type = ret_t.map(|t| t.apply(&subst));

                Ok((subst, ret_type))
            }
            Stmt::Assignment(x, f, e) => {
                let (subst_i, inferred) = e.infer_type(env, gen)?;

                // TODO: necessary? Probably not
                // let env = env.apply(&subst_i);
                let remembered = env
                    .get(x)
                    .ok_or(TypeError::Unbound(x.clone()))?.inner
                    .clone();

                let mut current = remembered;
                let subst_f = f.fields
                    .iter()
                    .fold(Ok(Substitution::new()), |acc, field| {
                        let subst = acc?;
                        let inner = Type::Polymorphic(gen.fresh());
                        match field {
                            Field::Head => {
                                let thing = Type::Array(Box::new(inner.clone()));
                                let subst_u = thing.unify_with(&current)?;
                                current = inner.apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::Tail => {
                                let thing = Type::Array(Box::new(inner.clone()));
                                let subst_u = thing.unify_with(&current)?;
                                current = Type::Array(Box::new(inner)).apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::First => {
                                let thing = Type::Tuple(Box::new(inner.clone()), Box::new(Type::Polymorphic(gen.fresh())));
                                let subst_u = thing.unify_with(&current)?;
                                current = inner.apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::Second => {
                                let thing = Type::Tuple(Box::new(Type::Polymorphic(gen.fresh())), Box::new(inner.clone()));
                                let subst_u = thing.unify_with(&current)?;
                                current = inner.apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                        }
                    })?;

                let subst_u = current.unify_with(&inferred)?;

                Ok((subst_u.compose(&subst_f.compose(&subst_i)), None))
            }
            Stmt::FunCall(fun_call) => {
                let (subst, _) = fun_call.infer_type(env, gen)?;
                Ok((subst, None))
            }
            Stmt::Return(e) => match e {
                None => Ok((Substitution::new(), Some(Type::Void))),
                Some(exp) => {
                    let (subst, inferred) = exp.infer_type(env, gen)?;
                    Ok((subst, Some(inferred)))
                }
            }
        }
    }
}

impl Infer for Exp {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Exp::Variable(id) => match env.get(id) {
                None => Err(TypeError::Unbound(id.clone())),
                Some(t) => Ok((Substitution::new(), t.instantiate(gen)))
            }
            Exp::Number(_) => Ok((Substitution::new(), Type::Int)),
            Exp::Character(_) => Ok((Substitution::new(), Type::Char)),
            Exp::False | Exp::True => Ok((Substitution::new(), Type::Bool)),
            Exp::FunCall(fun_call) => fun_call.infer_type(env, gen),
            Exp::Nil => Ok((Substitution::new(), Type::Array(Box::new(Type::Polymorphic(gen.fresh()))))),
            Exp::Tuple(l, r) => {
                let (l_subst, l_inferred) = l.infer_type(env, gen)?;
                let (r_subst, r_inferred) = r.infer_type(&env.apply(&l_subst), gen)?;
                let subst = r_subst.compose(&l_subst);
                // TODO: Apply substitutions to l_inferred?
                let l_inferred = l_inferred.apply(&subst);
                Ok((subst, Type::Tuple(Box::new(l_inferred), Box::new(r_inferred))))
            }
        }
    }
}

impl Infer for FunCall {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        let mut arg_types = env
            .get(&self.id)
            .ok_or(TypeError::Unbound(self.id.clone()))?
            .instantiate(gen)
            .unfold();

        let ret_type = arg_types
            .pop()
            .unwrap();

        let mut env = env.clone();
        // TODO: Error if wrong number of args
        let mut types = Vec::new();
        let subst_i = self.args
            .iter()
            .fold(Ok(Substitution::new()), |acc, exp| {
                let subst_a = acc?;
                let (subst_i, inferred) = exp.infer_type(&env, gen)?;
                let subst = subst_i.compose(&subst_a);
                env = env.apply(&subst);
                types.push(inferred);
                Ok(subst)
            })?;

        types.apply(&subst_i);
        // TODO: Necessary? Probably
        arg_types.apply(&subst_i);

        let subst_u = types
            .into_iter()
            .zip(&arg_types)
            .fold(Ok(Substitution::new()), |acc, (inferred, required)| {
                let subst = acc?;
                let s = inferred.unify_with(&required.apply(&subst))?;
                Ok(s.compose(&subst))
            })?;

        let subst = subst_u.compose(&subst_i);
        let t = ret_type.apply(&subst);
        Ok((subst, t))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::tree::Id;
    use crate::typer::{Type, TypeVariable};

    pub type Result<T, E = TypeError> = std::result::Result<T, E>;

    #[derive(Eq, PartialEq)]
    pub enum TypeError {
        Mismatch {
            expected: Type,
            found: Type,
        },
        Unbound(Id),
        Conflict(Id),
        Recursive(TypeVariable, Type),
    }

    impl fmt::Display for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                TypeError::Mismatch { expected, found } => write!(f, "Type mismatch: expected {:?}, found {:?}", expected, found),
                TypeError::Unbound(id) => write!(f, "Unbound variable {:?}", id),
                TypeError::Conflict(id) => write!(f, "Variable {:?} is defined more than once", id),
                TypeError::Recursive(v, t) => write!(f, "Occur check fails: {:?} vs {:?}", v, t),
            }
        }
    }

    impl Debug for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for TypeError {}
}

#[cfg(test)]
mod tests {
    use crate::typer::Type;

    #[test]
    fn unfold() {
        let t = Type::Function(Box::new(Type::Int), Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Array(Box::new(Type::Char))))));
        assert_eq!(vec![Type::Int, Type::Bool, Type::Array(Box::new(Type::Char))], t.unfold())
    }
}
