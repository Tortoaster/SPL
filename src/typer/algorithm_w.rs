use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use crate::lexer::Lexable;
use crate::parser::Id;
use crate::typer::error::{Result, TypeError};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TypeVariable(usize, BTreeSet<TypeClass>);

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

    pub fn impose(&mut self, class: TypeClass) {
        self.1.insert(class);
    }
}

pub struct Generator {
    current: usize,
}

impl Generator {
    pub fn new() -> Self {
        Generator {
            current: 0
        }
    }

    pub fn fresh(&mut self) -> TypeVariable {
        self.current += 1;
        TypeVariable(self.current, BTreeSet::new())
    }

    pub fn fresh_with(&mut self, classes: BTreeSet<TypeClass>) -> TypeVariable {
        let mut var = self.fresh();
        var.1 = classes;
        var
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
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
    pub fn generalize(&self, env: &Environment) -> PolyType {
        PolyType {
            variables: self
                .free_vars()
                .difference(&env.free_vars())
                .cloned()
                .collect(),
            inner: self.clone(),
        }
    }

    pub fn unify_with(&self, other: &Self) -> Result<Substitution> {
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
                let combined = v1.1.union(&v2.1).cloned().collect();
                let new = Type::Polymorphic(TypeVariable(v2.0, combined));
                Ok(v1.bind(&new)?.compose(&v2.bind(&new)?))
            }
            (Type::Polymorphic(v), t) | (t, Type::Polymorphic(v)) => v.bind(t),
            (t1, t2) => Err(TypeError::Mismatch { expected: t1.clone(), found: t2.clone() })
        }
    }

    fn implements(&self, class: &TypeClass) -> Result<bool> {
        if let Type::Polymorphic(var) = self {
            if var.1.contains(class) {
                return Ok(true);
            }
        }

        let result = match class {
            TypeClass::Any => true,
            TypeClass::Show => match self {
                Type::Int | Type::Char | Type::Bool => true,
                Type::Tuple(l, r) => l.implements(class)? && r.implements(class)?,
                Type::Array(a) => a.implements(class)?,
                _ => false
            }
            TypeClass::Eq => match self {
                Type::Int | Type::Bool | Type::Char => true,
                _ => false
            }
            TypeClass::Ord => match self {
                Type::Int | Type::Char => true,
                _ => false
            }
            // _ => return Err(TypeError::UndefinedClass(class.clone()))
        };

        Ok(result)
    }

    /// Returns a type into a vector of the argument types and the return type
    pub fn unfold(&self) -> Vec<Self> {
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
            Type::Function(a, b) => match **b {
                Type::Function(_, _) => format!("{} {}", a.format(poly_names), b.format(poly_names)),
                _ => format!("{} -> {}", a.format(poly_names), b.format(poly_names))
            }
            Type::Polymorphic(v) => format!("{}", poly_names.get(&v).unwrap_or(&'?'))
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format(&HashMap::new()))
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub enum TypeClass {
    Any,
    Show,
    Eq,
    Ord,
}

// impl TypeClass {
//     pub fn dependencies(&self) -> BTreeSet<TypeClass> {
//         match self {
//             TypeClass::Any => BTreeSet::new(),
//             TypeClass::Show => Some(TypeClass::Any).into_iter().collect(),
//             TypeClass::Eq => Some(TypeClass::Any).into_iter().collect(),
//             TypeClass::Ord => Some(TypeClass::Eq).into_iter().collect(),
//         }
//     }
//
//     pub fn methods(&self) -> Vec<Id> {
//         match self {
//             TypeClass::Any => Vec::new(),
//             TypeClass::Show => vec![Id("show".to_owned())],
//             TypeClass::Eq => vec![Id("eq".to_owned()), Id("ne".to_owned())],
//             TypeClass::Ord => vec![Id("lt".to_owned()), Id("gt".to_owned()), Id("le".to_owned()), Id("ge".to_owned())],
//         }
//     }
// }

impl fmt::Display for TypeClass {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeClass::Any => write!(f, "Any"),
            TypeClass::Show => write!(f, "Show"),
            TypeClass::Eq => write!(f, "Eq"),
            TypeClass::Ord => write!(f, "Ord")
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct PolyType {
    pub variables: BTreeSet<TypeVariable>,
    pub inner: Type,
}

impl PolyType {
    pub fn instantiate(&self, gen: &mut Generator) -> Type {
        let subst = self.variables
            .iter()
            .map(|var| (var.clone(), Type::Polymorphic(gen.fresh_with(var.1.clone()))))
            .collect();
        self.inner.apply(&subst)
    }
}

impl From<Type> for PolyType {
    fn from(inner: Type) -> Self {
        PolyType {
            variables: BTreeSet::new(),
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
                var.1.clone().into_iter().map(move |class| format!("{} {}", class, poly_names.get(&var).unwrap()))
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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub enum Space {
    Fun,
    Var,
}

#[derive(Clone, Debug)]
pub struct Environment(HashMap<(Id, Space), PolyType>);

impl Environment {
    pub fn new() -> Self {
        let mut env = Environment(HashMap::new());
        for (name, annotation) in vec![
            ("print", "Show a => a -> Void"),
            ("isEmpty", "[a] -> Bool"),
            ("hd", "[a] -> a"),
            ("tl", "[a] -> [a]"),
            ("fst", "(a, b) -> a"),
            ("snd", "(a, b) -> b"),
            ("not", "Bool -> Bool"),
            ("neg", "Int -> Int"),
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
            let fun_type = Type::parse_function(&mut annotation.tokenize().unwrap().peekable(), &mut Generator::new(), &mut HashMap::new()).unwrap();
            let scheme = fun_type.generalize(&mut env);
            env.insert((Id(name.to_owned()), Space::Fun), scheme);
        }
        env
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
    pub fn new() -> Self {
        Substitution(HashMap::new())
    }

    pub fn compose(&self, other: &Self) -> Self {
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
