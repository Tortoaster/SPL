use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use std::ops::{Deref, DerefMut};

use error::Result;

use crate::tree::{Exp, Id, SPL};
use crate::typer::error::TypeError;
use crate::lexer::Operator;
use std::iter::FromIterator;
use std::collections::hash_map::{RandomState, IntoIter};

trait Typable {
    fn free_variables(&self) -> HashSet<TypeVariable>;

    fn apply(&self, subst: &Substitution) -> Self;
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
struct TypeVariable(usize);

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
enum Type {
    Int,
    Bool,
    Char,
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Function(Box<Type>, Box<Type>),
    Variable(TypeVariable),
}

impl Type {
    fn most_general_unifier(&self, other: &Type) -> Result<Substitution> {
        match (self, other) {
            (Type::Int, Type::Int) | (Type::Bool, Type::Bool) | (Type::Char, Type::Char) => Ok(Substitution::new()),
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => Ok(l1.most_general_unifier(l2)?.compose(&r1.most_general_unifier(r2)?)),
            (Type::Array(t1), Type::Array(t2)) => t1.most_general_unifier(t2),
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                let arg = a1.most_general_unifier(a2)?;
                let res = b1.apply(&arg).most_general_unifier(&b2.apply(&arg))?;
                Ok(arg.compose(&res))
            }
            (Type::Variable(v), t) | (t, Type::Variable(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Unify(t1.clone(), t2.clone()))
        }
    }

    fn unfold(&self) -> Vec<&Type> {
        match self {
            Type::Function(a, b) => {
                let mut vec = vec![&**a];
                vec.append(&mut b.unfold());
                vec
            },
            _ => vec![self]
        }
    }
}

impl Typable for Type {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        match self {
            Type::Int | Type::Bool | Type::Char => HashSet::new(),
            Type::Tuple(l, r) => l.free_variables().union(&r.free_variables()).cloned().collect(),
            Type::Array(a) => a.free_variables(),
            Type::Function(a, b) => a.free_variables().union(&b.free_variables()).cloned().collect(),
            Type::Variable(v) => Some(*v).into_iter().collect()
        }
    }

    fn apply(&self, subst: &Substitution) -> Self {
        match self {
            Type::Int | Type::Bool | Type::Char => self.clone(),
            Type::Tuple(l, r) => Type::Tuple(Box::new(l.apply(subst)), Box::new(r.apply(subst))),
            Type::Array(a) => Type::Array(Box::new(a.apply(subst))),
            Type::Function(a, b) => Type::Function(Box::new(a.apply(subst)), Box::new(b.apply(subst))),
            Type::Variable(v) => subst.get(v).unwrap_or(self).clone()
        }
    }
}

struct PolyType {
    variables: Vec<TypeVariable>,
    inner: Type,
}

impl PolyType {
    fn instantiate(&self, generator: &mut Generator) -> Type {
        let fresh = std::iter::repeat_with(|| Type::Variable(generator.fresh()));
        let subst = Substitution(self.variables.iter().cloned().zip(fresh).collect());
        self.inner.apply(&subst)
    }
}

impl Typable for PolyType {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        self.inner.free_variables().into_iter().filter(|t| !self.variables.contains(t)).collect()
    }

    fn apply(&self, subst: &Substitution) -> Self {
        PolyType {
            variables: self.variables.clone(),
            inner: self.inner.apply(&Substitution(subst.iter().filter(|&(t, _)| !self.variables.contains(t)).map(|(k, v)| (k.clone(), v.clone())).collect())),
        }
    }
}

struct Environment(HashMap<Id, PolyType>);

impl Environment {
    fn new() -> Self {
        Environment(HashMap::new())
    }

    fn generalize(&self, instance: &Type) -> PolyType {
        let free = self.free_variables();
        PolyType {
            variables: instance.free_variables().into_iter().filter(|t| !free.contains(t)).collect(),
            inner: instance.clone(),
        }
    }

    fn type_check(&self, ast: &SPL, generator: &mut Generator) {
        ast.infer_type(self, generator);
    }
}

impl Typable for Environment {
    fn free_variables(&self) -> HashSet<TypeVariable> {
        self.values().flat_map(|t| t.free_variables()).collect()
    }

    fn apply(&self, subst: &Substitution) -> Self {
        Environment(self.iter().map(|(k, v)| (k.clone(), v.apply(subst))).collect())
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

    fn compose(&self, other: &Self) -> Substitution {
        let done = other.iter().map(|(k, v)| (k.clone(), v.apply(self)));
        Substitution(done.chain(self.iter().map(|(k, v)| (k.clone(), v.clone()))).collect())
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

struct Generator {
    current: usize
}

impl Generator {
    fn new() -> Self {
        Generator {
            current: 0
        }
    }

    fn fresh(&mut self) -> TypeVariable {
        self.current += 1;
        TypeVariable(self.current)
    }
}

trait Inferable {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type)>;
}

impl Inferable for SPL {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type), TypeError> {
        unimplemented!()
    }
}

impl Operator {
    fn get_type(&self, generator: &mut Generator) -> PolyType {
        match self {
            Operator::Not => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Bool), Box::new(Type::Bool))
            },
            Operator::Plus | Operator::Minus | Operator::Times | Operator::Divide | Operator::Modulo => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Int), Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Int))))
            },
            Operator::Equals | Operator::NotEqual => {
                let a = generator.fresh();
                PolyType {
                    variables: vec![a],
                    inner: Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Bool))))
                }
            }
            Operator::Smaller | Operator::Greater | Operator::SmallerEqual | Operator::GreaterEqual => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Int), Box::new(Type::Function(Box::new(Type::Int), Box::new(Type::Bool))))
            },
            Operator::And | Operator::Or => PolyType {
                variables: Vec::new(),
                inner: Type::Function(Box::new(Type::Bool), Box::new(Type::Function(Box::new(Type::Bool), Box::new(Type::Bool))))
            },
            Operator::Cons => {
                let a = generator.fresh();
                PolyType {
                    variables: vec![a],
                    inner: Type::Function(Box::new(Type::Variable(a)), Box::new(Type::Function(Box::new(Type::Array(Box::new(Type::Variable(a)))), Box::new(Type::Array(Box::new(Type::Variable(a)))))))
                }
            }
        }
    }
}

impl Inferable for Exp {
    fn infer_type(&self, environment: &Environment, generator: &mut Generator) -> Result<(Substitution, Type), TypeError> {
        match self {
            Exp::Variable(id) => match environment.get(id) {
                None => Err(TypeError::Unbound(id.clone())),
                Some(t) => Ok((Substitution::new(), t.instantiate(generator)))
            }
            Exp::BinaryOp(op, lhs, rhs) => {
                if let Type::Function(a, f) = op.get_type(generator).inner {
                    if let Type::Function(b, c) = *f {
                        let (s, t1) = lhs.infer_type(environment, generator)?;
                        let mut subst = s.compose(&t1.most_general_unifier(&a)?);
                        let (s, t2) = rhs.infer_type(&environment.apply(&subst), generator)?;
                        subst = subst.compose(&s.compose(&t2.most_general_unifier(&b)?));
                        Ok((subst, *c))
                    } else {
                        panic!("Impossible")
                    }
                } else {
                    panic!("Impossible")
                }
            }
            Exp::UnaryOp(op, rhs) => {
                if let Type::Function(a, b) = op.get_type(generator).inner {
                    let (s, t) = rhs.infer_type(environment, generator)?;
                    let subst = s.compose(&t.most_general_unifier(&a)?);
                    Ok((subst, *b))
                } else {
                    panic!("Impossible")
                }
            }
            Exp::Number(_) => Ok((Substitution::new(), Type::Int)),
            Exp::Character(_) => Ok((Substitution::new(), Type::Char)),
            Exp::False | Exp::True => Ok((Substitution::new(), Type::Bool)),
            Exp::FunCall(fun_call) => {
                match environment.get(&fun_call.id) {
                    None => Err(TypeError::Unbound(fun_call.id.clone())),
                    Some(pt) => {
                        let types = pt.inner.unfold();
                        let mut environment = environment.apply(&Substitution::new());
                        let subst: Result<Vec<Substitution>> = types.iter().copied().zip(&fun_call.args).map(|(t1, e)| {
                            let (s, t2) = e.infer_type(&environment, generator)?;
                            let subst = s.compose(&t1.most_general_unifier(&t2)?);
                            environment = environment.apply(&subst);
                            Ok(subst)
                        }).collect();
                        let subst = subst?.into_iter().flatten().collect();
                        Ok((subst, (*types.last().unwrap()).clone()))
                    }
                }
            }
            Exp::Nil => {
                let var = generator.fresh();
                let t = Type::Variable(var);
                let mut sub = Substitution::new();
                sub.insert(var, t.clone());
                Ok((sub, Type::Array(Box::new(t))))
            },
            Exp::Tuple(l, r) => {
                let (s1, t1) = l.infer_type(environment, generator)?;
                let (s2, t2) = r.infer_type(&environment.apply(&s1), generator)?;
                Ok((s1.compose(&s2), Type::Tuple(Box::new(t1), Box::new(t2))))
            }
        }
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
        self.into_iter()
    }
}

mod error {
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
