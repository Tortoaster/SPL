use std::collections::{HashMap, HashSet};
use std::collections::hash_map::IntoIter;
use std::fmt;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};
use std::str::FromStr;

use error::Result;

use crate::lexer::{Field, Lexable, Operator};
use crate::parser::error::ParseError;
use crate::parser::Parsable;
use crate::tree::{BasicType, Decl, Exp, FunCall, FunDecl, FunType, Id, RetType, SPL, Stmt, TypeAnnotation, VarDecl, VarType};
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

#[derive(Clone, Debug)]
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
    fn unify_with(&self, other: &Type) -> Result<Substitution> {
        match (self, other) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Char, Type::Char) => Ok(Substitution::new()),
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => {
                let subst_l = l1.unify_with(l2)?;
                let subst_r = r1.apply(&subst_l).unify_with(&r2.apply(&subst_l))?;
                Ok(subst_l.compose(&subst_r))
            },
            (Type::Array(t1), Type::Array(t2)) => t1.unify_with(t2),
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                let subst_a = a1.unify_with(a2)?;
                let subst_b = b1.apply(&subst_a).unify_with(&b2.apply(&subst_a))?;
                Ok(subst_a.compose(&subst_b))
            }
            (Type::Polymorphic(v), t) | (t, Type::Polymorphic(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Unify(t1.clone(), t2.clone()))
        }
    }

    fn unfold(&self) -> Vec<&Type> {
        match self {
            Type::Function(a, b) => {
                let mut vec = vec![&**a];
                vec.append(&mut b.unfold());
                vec
            }
            _ => vec![self]
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

#[derive(Clone, Debug)]
pub struct PolyType {
    variables: Vec<TypeVariable>,
    inner: Type,
}

impl PolyType {
    fn instantiate(&self, generator: &mut Generator) -> Type {
        let fresh = std::iter::repeat_with(|| Type::Polymorphic(generator.fresh()));
        let subst = Substitution(self.variables.iter().cloned().zip(fresh).collect());
        self.inner.apply(&subst)
    }
}

impl FromStr for PolyType {
    type Err = ParseError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let fun_type = FunType::parse(&mut s.tokenize().unwrap().peekable())?;

        let mut generator = Generator::new();
        let mut poly_names: HashMap<Id, TypeVariable> = HashMap::new();

        let arg_types: Vec<Type> = fun_type.arg_types
            .iter()
            .map(|t| t.transform(&mut generator, &mut poly_names))
            .collect();

        let ret_type = fun_type.ret_type.transform(&mut generator, &mut poly_names);

        let t = arg_types.into_iter().rfold(ret_type, |ret, arg| Type::Function(Box::new(arg), Box::new(ret)));
        Ok(PolyType { variables: poly_names.values().collect(), inner: t })
    }
}

impl fmt::Display for PolyType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let poly_names: HashMap<TypeVariable, char> = self.variables.iter().copied().zip('a'..'z').collect();
        write!(f, "{}", self.inner.format(&poly_names))
    }
}

#[derive(Clone, Debug)]
pub struct Environment(HashMap<Id, PolyType>);

impl Environment {
    pub fn new() -> Self {
        Environment(HashMap::new())
    }

    fn generalize(&self, instance: &Type) -> PolyType {
        let free = self.free_vars();
        PolyType {
            variables: instance
                .free_vars()
                .into_iter()
                .filter(|t| !free.contains(t))
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

struct Substitution(HashMap<TypeVariable, Type>);

impl Substitution {
    fn new() -> Self {
        Substitution(HashMap::new())
    }

    fn compose(&self, other: &Self) -> Self {
        // TODO: this way, or the other way around?
        self
            .iter()
            .map(|(k, v)| (*k, v.apply(&self)))
            .chain(other
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

trait Typed {
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

impl Typed for PolyType {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self.inner
            .free_vars()
            .into_iter()
            .filter(|t| !self.variables.contains(t))
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

impl InferMut for SPL {
    fn infer_type_mut(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        // Add prelude functions
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
            let t: PolyType = annotation.parse().unwrap();
            environment.insert(Id(name.to_owned()), environment.generalize(&t.instantiate(generator)))
        }

        // Add global variables and functions to scope
        self.decls.iter()
            .map(|decl| match decl {
                Decl::VarDecl(decl) => {
                    let v = generator.fresh();
                    let t = PolyType { variables: vec![v], inner: Type::Polymorphic(v) };
                    if environment.insert(decl.id.clone(), t).is_some() {
                        Err(TypeError::Conflict(decl.id.clone()))
                    } else {
                        Ok(())
                    }
                }
                Decl::FunDecl(decl) => {
                    let v = generator.fresh();
                    let (variables, inner) = decl.args.iter().fold(
                        (vec![v], Type::Polymorphic(v)),
                        |(mut vars, t), _| {
                            let a = generator.fresh();
                            vars.push(a);
                            (vars, Type::Function(Box::new(Type::Polymorphic(a)), Box::new(t)))
                        },
                    );
                    let t = PolyType { variables, inner };
                    if environment.insert(decl.id.clone(), t).is_some() {
                        Err(TypeError::Conflict(decl.id.clone()))
                    } else {
                        Ok(())
                    }
                    // TODO: check for doubly defined variables in functions
                }
            }).collect::<Result<()>>()?;

        // Infer types of inner declarations
        self.decls.iter().map(|decl| decl.infer_type(environment, generator)).collect::<Result<Vec<Type>>>()?;

        Ok(Type::Void)
    }
}

impl Infer for Decl {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer_type(environment, generator),
            Decl::FunDecl(fun_decl) => fun_decl.infer_type(environment, generator)
        }
    }
}

impl InferMut for VarDecl {
    fn infer_type_mut(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        let (subst_i, inferred) = self.exp.infer_type(environment, generator)?;
        let subst_u = inferred.unify_with(&self.var_type.transform(generator))?;
        let t = environment.generalize(&inferred.apply(&subst_i.compose(&subst_u)));
        environment.insert(self.id.clone(), t);
        Ok(Type::Void)
    }
}

impl Infer for FunDecl {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type)> {
        // Create local scope
        let mut local = environment.clone();
        let mut arg_types: Vec<Type> = local
            .get(&self.id)
            .ok_or(TypeError::Unbound(x.clone()))?.inner
            .unfold()
            .into_iter()
            .cloned()
            .collect();
        let ret_type = arg_types.pop().unwrap();
        let mut poly_names: HashMap<Id, TypeVariable> = HashMap::new();
        let (arg_annotations, ret_annotation) = match &self.fun_type {
            None => {
                let args: Vec<Option<Type>> = std::iter::repeat(None)
                    .take(self.args.len())
                    .collect();
                (args, None)
            },
            Some(fun_type) => {
                let args: Vec<Option<Type>> = fun_type.arg_types
                    .iter()
                    .map(|t| Some(t.transform(generator, &mut poly_names)))
                    .collect();
                (args, fun_type.ret_type.transform(generator, &mut poly_names))
            }
        };

        // Add arguments to local scope
        self.args
            .iter()
            .zip(arg_types.clone())
            .zip(arg_annotations)
            .map(|((arg, mut t), annotation)| {
                if let Some(a) = annotation {
                    let subst = t.unify_with(&a)?;
                    local.apply(&subst);
                    // TODO: Is this necessary?
                    t.apply(&subst);
                }
                let t = local.generalize(&t);
                local.insert(arg.clone(), t);
                Ok(())
            })
            .collect::<Result<()>>()?;

        // Add variable declarations to local scope
        self.var_decls.iter().map(|decl| decl.infer_type(&mut local, generator)).collect::<Result<Vec<Type>>>()?;

        // Infer types in inner statements
        self.stmts.iter().map(|decl| decl.infer_type(&mut local, generator)).collect::<Result<Vec<Type>>>()?;

        // Check return type
        // TODO: Check all paths for returns
        let returns = self.stmts.iter().flat_map(|stmt| stmt.iter()).flat_map(|ret| {
            if let Stmt::Return(exp) = ret {
                Some(exp.as_ref().map_or(Ok(Type::Void), |e| e.infer_type(&mut local, generator)))
            } else {
                None
            }
        }).collect::<Result<Vec<Type>>>()?;
        let mut initial = arg_types.last().unwrap().clone();
        if let Some(f) = &self.fun_type {
            let t = f.ret_type.transform(generator, &mut poly_names);
            let subst = initial.unify_with(&t)?;
            local.apply(&subst);
            initial.apply(&subst);
        }
        returns.into_iter()
            .fold(
                Ok((Substitution::new(), initial)),
                |r, t2| {
                    let (s, mut t1) = r?;
                    let subst = t1.unify_with(&t2)?;
                    t1.apply(&subst);
                    Ok((s.compose(subst), t1))
                },
            )?;

        // Delete local scope
        self.args.iter().for_each(|arg| {
            local.remove(arg);
        });
        self.var_decls.iter().for_each(|decl| {
            local.remove(&decl.id);
        });
        environment.extend(local.0);

        Ok(Type::Void)
    }
}

impl Infer for Vec<Stmt> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        let mut env = env.clone();
        let subst = self
            .iter()
            .inspect()
            .map(|e| {
                let (s, _) = e.infer_type(&env, gen)?;
                env = env.apply(&s);
                Ok(s)
            })
            .collect::<Result<Vec<Substitution>>>()?
            .into_iter()
            .fold(Substitution::new(), |acc, s| acc.compose(&s));
        Ok((subst, Type::Void))
    }
}

impl Infer for Stmt {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Stmt::If(c, t, e) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_i.compose(&subst_u);
                let env = &env.apply(&subst);
                let (subst_t, _) = t.infer_type_mut(env, gen);
                let env = &env.apply(&subst_t);
                let (subst_e, _) = t.infer_type_mut(env, gen);
                Ok((subst.compose(&subst_t).compose(&subst_e), Type::Void))
            }
            Stmt::While(c, t) => {
                let (subst_i, inferred) = c.infer_type(env, gen)?;
                let subst_u = inferred.unify_with(&Type::Bool)?;
                let subst = subst_i.compose(&subst_u);
                let env = &env.apply(&subst);
                let (subst_t, _) = t.infer_type(env, gen);
                Ok((subst.compose(&subst_t), Type::Void))
            }
            Stmt::Assignment(x, _, e) => {
                let (subst_i, inferred) = e.infer_type(env, gen)?;
                let remembered = &env
                    .get(x)
                    .ok_or(TypeError::Unbound(x.clone()))?.inner;
                let subst_u = remembered.unify_with(&inferred)?;
                let subst = subst_i.compose(&subst_u);
                // TODO: Implement fields
                // let env = &env.apply(&subst);
                // inferred.apply(&subst);
                // for field in &s.fields {
                //     match field {
                //         Field::Head => {
                //             let mut list = Type::Array(Box::new(Type::Polymorphic(gen.fresh())));
                //             let subst = inferred.unify(&list)?;
                //             env.apply(&subst);
                //             list.apply(&subst);
                //             if let Type::Array(t) = list {
                //                 inferred = *t;
                //             } else {
                //                 panic!("Impossible")
                //             }
                //         }
                //         Field::Tail => {
                //             let mut list = Type::Array(Box::new(Type::Polymorphic(gen.fresh())));
                //             let subst = inferred.unify(&list)?;
                //             env.apply(&subst);
                //             list.apply(&subst);
                //             inferred = list;
                //         }
                //         Field::First => {
                //             let mut tuple = Type::Tuple(Box::new(Type::Polymorphic(gen.fresh())), Box::new(Type::Polymorphic(gen.fresh())));
                //             let subst = inferred.unify(&tuple)?;
                //             env.apply(&subst);
                //             tuple.apply(&subst);
                //             if let Type::Tuple(t, _) = tuple {
                //                 inferred = *t;
                //             } else {
                //                 panic!("Impossible")
                //             }
                //         }
                //         Field::Second => {
                //             let mut tuple = Type::Tuple(Box::new(Type::Polymorphic(gen.fresh())), Box::new(Type::Polymorphic(gen.fresh())));
                //             let subst = inferred.unify(&tuple)?;
                //             env.apply(&subst);
                //             tuple.apply(&subst);
                //             if let Type::Tuple(_, t) = tuple {
                //                 inferred = *t;
                //             } else {
                //                 panic!("Impossible")
                //             }
                //         }
                //     }
                // }
                Ok((subst, Type::Void))
            }
            Stmt::FunCall(fun_call) => fun_call.infer_type(env, gen),
            Stmt::Return(_) => Ok((Substitution::new(), Type::Void))
        }
    }
}

impl Infer for Exp {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Exp::Variable(id) => match environment.get(id) {
                None => Err(TypeError::Unbound(id.clone())),
                Some(t) => Ok((Substitution::new(), t.instantiate(generator)))
            }
            Exp::Number(_) => Ok((Substitution::new(), Type::Int)),
            Exp::Character(_) => Ok((Substitution::new(), Type::Char)),
            Exp::False | Exp::True => Ok((Substitution::new(), Type::Bool)),
            Exp::FunCall(fun_call) => fun_call.infer_type(environment, generator),
            Exp::Nil => Ok((Substitution::new(), Type::Array(Box::new(Type::Polymorphic(generator.fresh()))))),
            Exp::Tuple(l, r) => {
                let (l_subst, l_inferred) = l.infer_type(environment, generator)?;
                let (r_subst, r_inferred) = r.infer_type(&environment.apply(&l_subst), generator)?;
                let subst = l_subst.compose(&r_subst);
                // TODO: Apply substitutions to l_inferred?
                Ok((subst, Type::Tuple(Box::new(l_inferred.apply(&subst)), Box::new(r_inferred))))
            }
        }
    }
}

impl Infer for FunCall {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type)> {
        let mut arg_types: Vec<Type> = environment
            .get(&self.id)
            .ok_or(Err(TypeError::Unbound(self.id.clone())))?.inner
            .unfold()
            .into_iter()
            .cloned()
            .collect();

        let ret_type = arg_types
            .pop()
            .unwrap();

        let subst = self.args
            .iter()
            .zip(arg_types)
            .map(|(e, t)| {
                let (subst_i, inferred) = e.infer_type(environment, generator)?;
                let subst_u = inferred.unify_with(&t)?;
                Ok(subst_i.compose(&subst_u))
            })
            .collect::<Result<Vec<Substitution>>>()?
            .into_iter()
            .fold(Substitution::new(), |acc, subst| acc.compose(&subst));

        Ok((subst, ret_type))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::tree::Id;
    use crate::typer::{Type, TypeVariable};

    pub type Result<T, E = TypeError> = std::result::Result<T, E>;

    pub enum TypeError {
        Unify(Type, Type),
        Unbound(Id),
        Conflict(Id),
        Recursive(TypeVariable, Type),
    }

    impl fmt::Display for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                TypeError::Unify(t1, t2) => write!(f, "Types {:?} and {:?} do not unify", t1, t2),
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
