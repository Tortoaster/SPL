use std::collections::{HashMap, HashSet};
use std::fmt;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use error::Result;

use crate::lexer::{Lexable, Field};
use crate::parser::Parsable;
use crate::tree::{Decl, Exp, FunCall, FunDecl, FunType, Id, SPL, Stmt, VarDecl};
use crate::typer::error::TypeError;

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable(usize, Vec<Id>);

impl TypeVariable {
    fn bind(&self, to: &Type) -> Result<Substitution> {
        if let Type::Polymorphic(v) = to {
            if *self == *v {
                return Ok(Substitution::new());
            }
        }

        for class in &self.1 {
            if !to.implements(class)? {
                return Err(TypeError::TypeClass { found: to.clone(), class: class.clone() });
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
        TypeVariable(self.current, Vec::new())
    }

    pub fn fresh_with(&mut self, classes: Vec<Id>) -> TypeVariable {
        let mut var = self.fresh();
        var.1 = classes;
        var
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
            (Type::Polymorphic(v1), Type::Polymorphic(v2)) => {
                let combined: HashSet<Id> = v1.1
                    .iter()
                    .cloned()
                    .chain(v2.1.clone())
                    .collect();
                let new = Type::Polymorphic(TypeVariable(v2.0, combined.into_iter().collect()));
                // TODO: Bind old value of v2 to new value of v2?
                Ok(v1.bind(&new)?.compose(&v2.bind(&new)?))
            },
            (Type::Polymorphic(v), t) | (t, Type::Polymorphic(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Mismatch { expected: t1.clone(), found: t2.clone() })
        }
    }

    fn implements(&self, class: &Id) -> Result<bool> {
        if let Type::Polymorphic(var) = self {
            if var.1.contains(class) {
                return Ok(true);
            }
        }

        let result = match class.0.as_str() {
            "Eq" => match self {
                Type::Int | Type::Bool | Type::Char => true,
                _ => false
            }
            "Ord" => match self {
                Type::Int | Type::Char => true,
                _ => false
            }
            "Show" => match self {
                Type::Int | Type::Char | Type::Bool => true,
                Type::Tuple(l, r) => l.implements(class)? && r.implements(class)?,
                Type::Array(a) => a.implements(class)?,
                _ => false
            }
            _ => return Err(TypeError::UndefinedClass(class.clone()))
        };

        Ok(result)
    }

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

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct PolyType {
    pub variables: Vec<TypeVariable>,
    pub inner: Type,
}

// TODO: Functions may not yet be generalized when they are called, which may change their type, and that is wrong. Can this be solved with topological sorting?

impl PolyType {
    pub fn instantiate(&self, gen: &mut Generator) -> Type {
        let subst = Substitution(self.variables
            .iter()
            .cloned()
            .map(|var| (var.clone(), Type::Polymorphic(gen.fresh_with(var.1))))
            .collect());
        self.inner.apply(&subst)
    }
}

impl From<Type> for PolyType {
    fn from(inner: Type) -> Self {
        PolyType {
            variables: Vec::new(),
            inner,
        }
    }
}

impl fmt::Display for PolyType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let poly_names: HashMap<TypeVariable, char> = self.variables
            .iter()
            .cloned()
            .zip('a'..'z')
            .collect();
        let mut type_classes: Vec<String> = self.variables
            .iter()
            .cloned()
            .filter(|var| !var.1.is_empty())
            .flat_map(|var| {
                let poly_names = &poly_names;
                var.1.clone().into_iter().map(move |class| format!("{} {}", class.0, poly_names.get(&var).unwrap()))
            })
            .collect();
        let x = if type_classes.is_empty() {
            String::new()
        } else {
            type_classes.sort();
            let mut s: String = type_classes.join(", ");
            s.push_str(" => ");
            s
        };
        write!(f, "{}{}", x, self.inner.format(&poly_names))
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Space {
    Fun,
    Var
}

#[derive(Clone, Debug)]
pub struct Environment(HashMap<(Id, Space), PolyType>);

impl Environment {
    pub fn new(gen: &mut Generator) -> Self {
        let mut env = Environment(HashMap::new());
        for (name, annotation) in vec![
            ("print", "Show a => a -> Void"),
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
            ("eq", "Eq a => a a -> Bool"),
            ("ne", "Eq a => a a -> Bool"),
            ("lt", "Ord a => a a -> Bool"),
            ("gt", "Ord a => a a -> Bool"),
            ("le", "Ord a => a a -> Bool"),
            ("ge", "Ord a => a a -> Bool"),
            ("and", "Bool Bool -> Bool"),
            ("or", "Bool Bool -> Bool"),
            ("cons", "a [a] -> [a]"),
        ] {
            let fun_type = FunType::parse(&mut annotation.tokenize().unwrap().peekable()).unwrap();
            env.insert((Id(name.to_owned()), Space::Fun), fun_type.transform(gen));
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
    type Target = HashMap<(Id, Space), PolyType>;

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
            .map(|(k, v)| (k.clone(), v.apply(&self)))
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
            Type::Polymorphic(v) => Some(v.clone()).into_iter().collect(),
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
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<(Type, bool)>)>;
}

impl InferMut for SPL {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        // Add global variables and functions to scope
        self.decls.iter()
            .map(|decl| match decl {
                Decl::VarDecl(decl) => {
                    // TODO: These are re-inserted in VarDecl
                    if env.insert((decl.id.clone(), Space::Var), decl.var_type.transform(gen).into()).is_some() {
                        Err(TypeError::Conflict(decl.id.clone()))
                    } else {
                        Ok(())
                    }
                }
                Decl::FunDecl(decl) => {
                    let inner = match &decl.fun_type {
                        None => {
                            let args: Vec<Type> = std::iter::repeat_with(|| Type::Polymorphic(gen.fresh()))
                                .take(decl.args.len())
                                .collect();
                            args
                                .into_iter()
                                .rfold(Type::Polymorphic(gen.fresh()), |t, annotation| Type::Function(Box::new(annotation), Box::new(t)))
                        }
                        Some(fun_type) => {
                            fun_type.transform(gen).inner
                        }
                    };
                    if env.insert((decl.id.clone(), Space::Fun), inner.into()).is_some() {
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
        env.insert((self.id.clone(), Space::Var), t);
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
            .get(&(self.id.clone(), Space::Fun))
            .ok_or(TypeError::Unbound(self.id.clone()))?.inner
            .unfold();
        let ret_type = arg_types.pop().unwrap();

        // Add arguments to local scope
        local.extend(self.args
            .iter()
            .cloned()
            .map(|id| (id, Space::Var))
            .zip(arg_types
                .into_iter()
                .map(|arg| arg.into())));

        // Add variable declarations to local scope
        self.var_decls
            .iter()
            .map(|decl| decl.infer_type_mut(&mut local, gen))
            .collect::<Result<Vec<Type>>>()?;

        // Infer types in inner statements
        let (subst_i, result) = self.stmts.try_infer_type(&local, gen)?;

        // Check return type
        let (inferred, complete) = result.unwrap_or((Type::Void, true));
        if !complete {
            return Err(TypeError::Incomplete(self.id.clone()));
        }
        let subst_r = ret_type.unify_with(&inferred)?;

        // Generalize function
        *env = env.apply(&subst_r.compose(&subst_i));
        let t = env.remove(&(self.id.clone(), Space::Fun)).unwrap();
        let new = env.generalize(&t.inner);
        env.insert((self.id.clone(), Space::Fun), new);

        Ok(Type::Void)
    }
}

trait Combine {
    fn combine_with(&self, other: &Self, both: bool) -> Result<(Substitution, Option<(Type, bool)>)>;
}

impl Combine for Option<(Type, bool)> {
    fn combine_with(&self, other: &Self, both: bool) -> Result<(Substitution, Option<(Type, bool)>)> {
        match (self, other) {
            (Some((t1, b1)), Some((t2, b2))) => {
                Ok((t1.unify_with(t2)?, Some((t1.clone(), if both { *b1 && *b2 } else { *b1 || *b2 }))))
            }
            (Some((t, b)), None) | (None, Some((t, b))) => {
                Ok((Substitution::new(), Some((t.clone(), if both { false } else { *b }))))
            }
            _ => Ok((Substitution::new(), None))
        }
    }
}

impl TryInfer for Vec<Stmt> {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<(Type, bool)>)> {
        let mut env = env.clone();
        let mut current: Option<(Type, bool)> = None;

        let subst = self
            .iter()
            .fold(Ok(Substitution::new()), |acc, stmt| {
                let subst_a = acc?;

                let (subst_i, result) = stmt.try_infer_type(&env, gen)?;

                let (subst_u, new) = current.combine_with(&result, false)?;

                let subst = subst_u.compose(&subst_i.compose(&subst_a));
                env = env.apply(&subst);

                current = new;
                if let Some((t, b)) = &current {
                    current = Some((t.apply(&subst), *b));
                }

                Ok(subst)
            })?;

        Ok((subst, current))
    }
}

impl TryInfer for Stmt {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<(Type, bool)>)> {
        match self {
            Stmt::If(c, t, e) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer_type(env, gen)?;
                let env = &env.apply(&subst_t);

                let (subst_e, ret_e) = e.try_infer_type(env, gen)?;

                let (subst_r, mut ret_type) = ret_t.combine_with(&ret_e, true)?;

                let subst = subst_r.compose(&subst_e.compose(&subst_t.compose(&subst)));

                if let Some((t, b)) = &ret_type {
                    ret_type = Some((t.apply(&subst), *b));
                }

                Ok((subst, ret_type))
            }
            Stmt::While(c, t) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer_type(env, gen)?;

                let subst = subst_t.compose(&subst);
                let ret_type = ret_t.map(|(t, b)| (t.apply(&subst), b));

                Ok((subst, ret_type))
            }
            Stmt::Assignment(x, f, e) => {
                let (subst_i, inferred) = e.infer_type(env, gen)?;

                // TODO: necessary?
                let env = env.apply(&subst_i);
                let remembered = env
                    .get(&(x.clone(), Space::Var))
                    .ok_or(TypeError::Unbound(x.clone()))?.inner
                    .clone();

                let mut current = remembered;
                let subst_f = f
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
                None => Ok((Substitution::new(), Some((Type::Void, true)))),
                Some(exp) => {
                    let (subst, inferred) = exp.infer_type(env, gen)?;
                    Ok((subst, Some((inferred, true))))
                }
            }
        }
    }
}

impl Infer for Exp {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Exp::Variable(id) => match env.get(&(id.clone(), Space::Var)) {
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
            .get(&(self.id.clone(), Space::Fun))
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
                // TODO: Subst is bigger than necessary?
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
        TypeClass {
            found: Type,
            class: Id
        },
        Unbound(Id),
        Conflict(Id),
        Recursive(TypeVariable, Type),
        Incomplete(Id),
        UndefinedClass(Id),
    }

    impl fmt::Display for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                TypeError::Mismatch { expected, found } => write!(f, "Type mismatch: expected {:?}, found {:?}", expected, found),
                TypeError::TypeClass { found, class } => write!(f, "Type {:?} does not implement {:?}", found, class),
                TypeError::Unbound(id) => write!(f, "Unbound variable {:?}", id),
                TypeError::Conflict(id) => write!(f, "Variable {:?} is defined more than once", id),
                TypeError::Recursive(v, t) => write!(f, "Occur check fails: {:?} vs {:?}", v, t),
                TypeError::Incomplete(id) => write!(f, "Function {:?} does not return a correct value in all paths", id),
                TypeError::UndefinedClass(id) => write!(f, "Type class {:?} not found", id),
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
