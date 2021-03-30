use std::collections::{HashMap, HashSet};
use std::collections::hash_map::IntoIter;
use std::hash::Hash;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use error::Result;

use crate::lexer::{Operator, Field};
use crate::tree::{Exp, Id, SPL, Stmt, Decl, VarDecl, FunDecl, FunCall, FunType};
use crate::typer::error::TypeError;

trait Typable {
    fn free_variables(&self) -> HashSet<TypeVariable>;

    fn apply(&mut self, subst: &Substitution);
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct TypeVariable(usize);

impl TypeVariable {
    fn bind(&self, to: &Type) -> Result<Substitution> {
        if let Type::Variable(v) = to {
            if *self == *v {
                return Ok(Substitution::new());
            }
        }

        if to.free_variables().contains(self) {
            return Err(TypeError::Recursive(self.clone(), to.clone()));
        }

        let mut s = Substitution::new();
        s.insert(self.clone(), to.clone());
        Ok(s)
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
    Variable(TypeVariable),
}

impl Type {
    fn unify(&self, other: &Type) -> Result<Substitution> {
        match (self, other) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Char, Type::Char) => Ok(Substitution::new()),
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => Ok(l1.unify(l2)?.compose(r1.unify(r2)?)),
            (Type::Array(t1), Type::Array(t2)) => t1.unify(t2),
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                let arg = a1.unify(a2)?;
                // Is applying necessary?
                let mut b1 = b1.clone();
                b1.apply(&arg);
                let mut b2 = b2.clone();
                b2.apply(&arg);
                let res = b1.unify(&b2)?;
                Ok(arg.compose(res))
            }
            (Type::Variable(v), t) | (t, Type::Variable(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Unify(t1.clone(), t2.clone()))
        }
    }

    fn unfold(self) -> Vec<Type> {
        match self {
            Type::Function(a, b) => {
                let mut vec = vec![*a];
                vec.append(&mut b.unfold());
                vec
            }
            _ => vec![self]
        }
    }
}

impl Typable for Type {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        match self {
            Type::Void | Type::Int | Type::Bool | Type::Char => HashSet::new(),
            Type::Tuple(l, r) => l.free_variables().union(&r.free_variables()).cloned().collect(),
            Type::Array(a) => a.free_variables(),
            Type::Function(a, b) => a.free_variables().union(&b.free_variables()).cloned().collect(),
            Type::Variable(v) => Some(*v).into_iter().collect(),
        }
    }

    fn apply(&mut self, subst: &Substitution) {
        match self {
            Type::Void | Type::Int | Type::Bool | Type::Char => (),
            Type::Tuple(l, r) => {
                l.apply(subst);
                r.apply(subst);
            }
            Type::Array(a) => a.apply(subst),
            Type::Function(a, b) => {
                a.apply(subst);
                b.apply(subst);
            }
            Type::Variable(v) => if let Some(t) = subst.get(v) {
                *self = t.clone();
            }
        }
    }
}

#[derive(Clone)]
pub struct PolyType {
    variables: Vec<TypeVariable>,
    inner: Type,
}

impl PolyType {
    fn instantiate(mut self, generator: &mut Generator) -> Type {
        let fresh = std::iter::repeat_with(|| Type::Variable(generator.fresh()));
        let subst = Substitution(self.variables.into_iter().zip(fresh).collect());
        self.inner.apply(&subst);
        self.inner
    }
}

impl Typable for PolyType {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        self.inner.free_variables().into_iter().filter(|t| !self.variables.contains(t)).collect()
    }

    fn apply(&mut self, subst: &Substitution) {
        self.inner.apply(
            &Substitution(
                subst.iter()
                    .filter(|&(t, _)| !self.variables.contains(t))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect()
            )
        );
    }
}

#[derive(Clone)]
pub struct Environment(HashMap<Id, PolyType>);

impl Environment {
    pub fn new() -> Self {
        Environment(HashMap::new())
    }

    fn generalize(&self, instance: &Type) -> PolyType {
        let free = self.free_variables();
        PolyType {
            variables: instance.free_variables().into_iter().filter(|t| !free.contains(t)).collect(),
            inner: instance.clone(),
        }
    }
}

impl Typable for Environment {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        self.values().flat_map(|t| t.free_variables()).collect()
    }

    fn apply(&mut self, subst: &Substitution) {
        self.iter_mut().for_each(|(_, v)| {
            v.apply(subst);
        });
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

    fn compose(self, mut other: Self) -> Substitution {
        other.iter_mut().for_each(|(_, v)| v.apply(&self));
        other.into_iter().chain(self).collect()
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

pub struct Generator {
    current: usize
}

impl Generator {
    pub fn new() -> Self {
        Generator {
            current: 0
        }
    }

    fn fresh(&mut self) -> TypeVariable {
        self.current += 1;
        TypeVariable(self.current)
    }
}

pub trait Inferable {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type>;
}

impl Inferable for SPL {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        // TODO: Find all global functions and variables
        self.decls.iter().map(|decl| decl.infer_type(environment, generator)).collect::<Result<Vec<Type>>>()?;
        Ok(Type::Void)
    }
}

impl Inferable for Decl {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer_type(environment, generator),
            Decl::FunDecl(fun_decl) => fun_decl.infer_type(environment, generator)
        }
    }
}

impl Inferable for VarDecl {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        let t = self.exp.infer_type(environment, generator)?;
        // TODO: Check type annotation
        environment.insert(self.id.clone(), PolyType { variables: Vec::new(), inner: t });
        Ok(Type::Void)
    }
}

impl Inferable for FunDecl {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        // Create local scope
        let mut local = environment.clone();

        // Add arguments to local scope
        self.args.iter().zip(match &self.fun_type {
            None => std::iter::repeat(None).take(self.args.len()).collect::<Vec<Option<&Type>>>(),
            Some(t) => t.arg_types.iter().map(|t| Some(t)).collect::<Vec<Option<&Type>>>()
        }).for_each(|(arg, annotation)| {
            let t = match annotation {
                None => {
                    let v = generator.fresh();
                    PolyType { variables: vec![v], inner: Type::Variable(v) }
                }
                // Use generalize?
                Some(t) => local.generalize(t)
            };
            local.insert(arg.clone(), t);
        });

        // Add variable declarations to local scope
        self.var_decls.iter().map(|decl| decl.infer_type(&mut local, generator)).collect::<Result<Vec<Type>>>()?;

        // Infer types in inner statements
        self.stmts.iter().map(|decl| decl.infer_type(&mut local, generator)).collect::<Result<Vec<Type>>>()?;

        // Check return type
        let returns = self.stmts.iter().flat_map(|stmt| stmt.iter()).flat_map(|ret| {
            if let Stmt::Return(exp) = ret {
                Some(exp.as_ref().map_or(Ok(Type::Void), |e| e.infer_type(environment, generator)))
            } else {
                None
            }
        }).collect::<Result<Vec<Type>>>()?;
        returns.into_iter()
            .fold(
                Ok((Substitution::new(), self.fun_type.map_or(Type::Variable(generator.fresh()), |t| t.ret_type))),
                |r, mut t2| {
                    let (s, t1) = r?;
                    let subst = t1.unify(&t2)?;
                    t2.apply(&subst);
                    Ok((s.compose(subst), t2))
                }
            )?;
        // TODO: Delete local scope
        Ok(Type::Void)
    }
}

impl Inferable for Stmt {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        match self {
            Stmt::If(c, t, e) => {
                let inferred = c.infer_type(environment, generator)?;
                environment.apply(&inferred.unify(&Type::Bool)?);
                t.iter().map(|e| e.infer_type(environment, generator)).collect::<Result<Vec<Type>>>()?;
                e.iter().map(|e| e.infer_type(environment, generator)).collect::<Result<Vec<Type>>>()?;
                Ok(Type::Void)
            }
            Stmt::While(c, t) => {
                let inferred = c.infer_type(environment, generator)?;
                environment.apply(&inferred.unify(&Type::Bool)?);
                t.iter().map(|e| e.infer_type(environment, generator)).collect::<Result<Vec<Type>>>()?;
                Ok(Type::Void)
            }
            Stmt::Assignment(x, s, e) => {
                let mut inferred = e.infer_type(environment, generator)?;
                let remembered = environment.get(x).ok_or(TypeError::Unbound(x.clone()))?;
                let subst = inferred.unify(&remembered.inner)?;
                environment.apply(&subst);
                inferred.apply(&subst);
                for field in &s.fields {
                    match field {
                        Field::Head => {
                            let mut list = Type::Array(Box::new(Type::Variable(generator.fresh())));
                            let subst = inferred.unify(&list)?;
                            environment.apply(&subst);
                            list.apply(&subst);
                            if let Type::Array(t) = list {
                                inferred = *t;
                            } else {
                                panic!("Impossible")
                            }
                        }
                        Field::Tail => {
                            let mut list = Type::Array(Box::new(Type::Variable(generator.fresh())));
                            let subst = inferred.unify(&list)?;
                            environment.apply(&subst);
                            list.apply(&subst);
                            inferred = list;
                        }
                        Field::First => {
                            let mut tuple = Type::Tuple(Box::new(Type::Variable(generator.fresh())), Box::new(Type::Variable(generator.fresh())));
                            let subst = inferred.unify(&tuple)?;
                            environment.apply(&subst);
                            tuple.apply(&subst);
                            if let Type::Tuple(t, _) = tuple {
                                inferred = *t;
                            } else {
                                panic!("Impossible")
                            }
                        }
                        Field::Second => {
                            let mut tuple = Type::Tuple(Box::new(Type::Variable(generator.fresh())), Box::new(Type::Variable(generator.fresh())));
                            let subst = inferred.unify(&tuple)?;
                            environment.apply(&subst);
                            tuple.apply(&subst);
                            if let Type::Tuple(_, t) = tuple {
                                inferred = *t;
                            } else {
                                panic!("Impossible")
                            }
                        }
                    }
                }
                Ok(Type::Void)
            }
            Stmt::FunCall(fun_call) => fun_call.infer_type(environment, generator),
            Stmt::Return(_) => Ok(Type::Void)
        }
    }
}

impl Operator {
    fn get_type(&self, generator: &mut Generator) -> PolyType {
        match self {
            Operator::Not => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Bool), Box::new(Type::Bool)),
            },
            Operator::Plus | Operator::Minus | Operator::Times | Operator::Divide | Operator::Modulo => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Int), Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Int)))),
            },
            Operator::Equals | Operator::NotEqual => {
                let a = generator.fresh();
                PolyType {
                    variables: vec![a],
                    inner: Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Bool)))),
                }
            }
            Operator::Smaller | Operator::Greater | Operator::SmallerEqual | Operator::GreaterEqual => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Int), Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool)))),
            },
            Operator::And | Operator::Or => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Bool), Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Bool)))),
            },
            Operator::Cons => {
                let a = generator.fresh();
                PolyType {
                    variables: vec![a],
                    inner: Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Function(Box::new(Type::Array(Box::new(Type::Variable(a)))), Box::new(Type::Array(Box::new(Type::Variable(a))))))),
                }
            }
        }
    }
}

impl Inferable for Exp {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type> {
        match self {
            Exp::Variable(id) => match environment.get(id) {
                None => Err(TypeError::Unbound(id.clone())),
                Some(t) => Ok(t.clone().instantiate(generator))
            }
            Exp::BinaryOp(op, lhs, rhs) => {
                if let Type::Function(a, f) = op.get_type(generator).inner {
                    if let Type::Function(b, mut c) = *f {
                        let t1 = lhs.infer_type(environment, generator)?;
                        let subst_a = t1.unify(&a)?;
                        environment.apply(&subst_a);
                        let t2 = rhs.infer_type(environment, generator)?;
                        let subst_b = t2.unify(&b)?;
                        environment.apply(&subst_b);
                        c.apply(&subst_a.compose(subst_b));
                        Ok(*c)
                    } else {
                        panic!("Impossible")
                    }
                } else {
                    panic!("Impossible")
                }
            }
            Exp::UnaryOp(op, rhs) => {
                if let Type::Function(a, mut b) = op.get_type(generator).inner {
                    let t = rhs.infer_type(environment, generator)?;
                    let subst = t.unify(&a)?;
                    environment.apply(&subst);
                    b.apply(&subst);
                    Ok(*b)
                } else {
                    panic!("Impossible")
                }
            }
            Exp::Number(_) => Ok(Type::Int),
            Exp::Character(_) => Ok(Type::Char),
            Exp::False | Exp::True => Ok(Type::Bool),
            Exp::FunCall(fun_call) => fun_call.infer_type(environment, generator),
            Exp::Nil => Ok(Type::Array(Box::new(Type::Variable(generator.fresh())))),
            Exp::Tuple(l, r) => {
                let t1 = l.infer_type(environment, generator)?;
                let t2 = r.infer_type(environment, generator)?;
                // TODO: apply substitutions to all returns
                Ok(Type::Tuple(Box::new(t1), Box::new(t2)))
            }
        }
    }
}

impl Inferable for FunCall {
    fn infer_type(&self, environment: &mut Environment, generator: &mut Generator) -> Result<Type, TypeError> {
        let types = match environment.get(&self.id) {
            None => return Err(TypeError::Unbound(self.id.clone())),
            Some(t) => t.clone()
        }.inner.unfold();
        self.args.iter().zip(&types).map(|(e, t)| {
            let found = e.infer_type(environment, generator)?;
            environment.apply(&found.unify(&t)?);
            Ok(())
        }).collect::<Result<()>>()?;
        Ok(types.last().unwrap().to_owned())
    }
}

impl FromIterator<(TypeVariable, Type)> for Substitution {
    fn from_iter<T: IntoIterator<Item=(TypeVariable, Type)>>(iter: T) -> Self {
        Substitution(iter.into_iter().collect())
    }
}

impl IntoIterator for Substitution {
    type Item = (TypeVariable, Type);
    type IntoIter = IntoIter<TypeVariable, Type>;

    fn into_iter(self) -> Self::IntoIter {
        let Substitution(m) = self;
        m.into_iter()
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
        Recursive(TypeVariable, Type),
    }

    impl fmt::Display for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                TypeError::Unify(t1, t2) => write!(f, "Types {:?} and {:?} do not unify", t1, t2),
                TypeError::Unbound(id) => write!(f, "Unbound variable {:?}", id),
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
