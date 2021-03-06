use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt;
use std::iter::FromIterator;
use std::ops::{Deref, DerefMut};

use crate::lexer::Lexable;
use crate::parser::Id;
use crate::position::Pos;
use crate::typer::error::{Result, TypeError};

#[derive(Clone, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub struct TypeVariable(usize, pub BTreeSet<TypeClass>);

impl<'a> TypeVariable {
    fn bind(&self, to: &PType<'a>) -> Result<'a, Substitution<'a>> {
        if let Type::Polymorphic(v) = &to.content {
            if *self == *v {
                return Ok(Substitution::new());
            }
        }

        for class in &self.1 {
            if !to.implements(class)? {
                return Err(to
                    .with(TypeError::TypeClass {
                        found: to.content.clone(),
                        class: class.clone(),
                    })
                );
            }
        }

        if to.free_vars().contains(self) {
            return Err(to.with(TypeError::Recursive(self.clone(), to.content.clone())));
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

pub type PType<'a> = Pos<'a, Type<'a>>;

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub enum Type<'a> {
    Void,
    Int,
    Bool,
    Char,
    Tuple(Box<PType<'a>>, Box<PType<'a>>),
    List(Box<PType<'a>>),
    Function(Box<PType<'a>>, Box<PType<'a>>),
    Polymorphic(TypeVariable),
}

impl<'a> Type<'a> {
    fn implements(&self, class: &TypeClass) -> Result<'a, bool> {
        if let Type::Polymorphic(var) = self {
            if var.1.contains(class) {
                return Ok(true);
            }
        }

        let result = match class {
            TypeClass::Show | TypeClass::Eq => match self {
                Type::Int | Type::Char | Type::Bool => true,
                Type::Tuple(l, r) => l.implements(class)? && r.implements(class)?,
                Type::List(a) => a.implements(class)?,
                _ => false
            }
            TypeClass::Ord => match self {
                Type::Int | Type::Char => true,
                _ => false
            }
        };

        Ok(result)
    }

    fn format(&self, poly_names: &HashMap<TypeVariable, char>) -> String {
        match self {
            Type::Void => format!("Void"),
            Type::Int => format!("Int"),
            Type::Bool => format!("Bool"),
            Type::Char => format!("Char"),
            Type::Tuple(l, r) =>
                format!("({}, {})", l.format(poly_names), r.format(poly_names)),
            Type::List(a) => format!("[{}]", a.format(poly_names)),
            Type::Function(a, b) => match b.content {
                Type::Function(_, _) => format!("{} {}", a.format(poly_names), b.format(poly_names)),
                _ => format!("{} -> {}", a.format(poly_names), b.format(poly_names))
            }
            Type::Polymorphic(v) => format!("{}", poly_names.get(&v).unwrap_or(&'?'))
        }
    }
}

impl<'a> PType<'a> {
    pub fn unify_with(&self, other: &Self) -> Result<'a, Substitution<'a>> {
        match (&self.content, &other.content) {
            (Type::Void, Type::Void) |
            (Type::Int, Type::Int) |
            (Type::Bool, Type::Bool) |
            (Type::Char, Type::Char) => Ok(Substitution::new()),
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => {
                let subst_l = l1.unify_with(l2)?;
                let subst_r = r1.apply(&subst_l).unify_with(&r2.apply(&subst_l))?;
                Ok(subst_r.compose(&subst_l))
            }
            (Type::List(t1), Type::List(t2)) => t1.unify_with(t2),
            (Type::Function(a1, b1), Type::Function(a2, b2)) => {
                let subst_a = a1.unify_with(a2)?;
                let subst_b = b1.apply(&subst_a).unify_with(&b2.apply(&subst_a))?;
                Ok(subst_b.compose(&subst_a))
            }
            (Type::Polymorphic(v1), Type::Polymorphic(v2)) => {
                let combined = v1.1.union(&v2.1).cloned().collect();
                let new = other.with(Type::Polymorphic(TypeVariable(v2.0, combined)));
                Ok(v1.bind(&new)?.compose(&v2.bind(&new)?))
            }
            (Type::Polymorphic(v), t) => v.bind(&other.with(t.clone())),
            (t, Type::Polymorphic(v)) => v.bind(&self.with(t.clone())),
            (t1, t2) => Err(self.with(TypeError::Mismatch { expected: t2.clone(), found: t1.clone() }))
        }
    }

    /// Finds out what substitution is necessary for this type to become the other type.
    /// This assumes the structure of the types is the same.
    pub fn find_substitution(&self, other: &Self) -> Substitution<'a> {
        match (&self.content, &other.content) {
            (Type::Tuple(l1, r1), Type::Tuple(l2, r2)) => l1
                .find_substitution(l2)
                .compose(&r1.find_substitution(r2)),
            (Type::List(a1), Type::List(a2)) => a1.find_substitution(a2),
            (Type::Function(arg1, res1), Type::Function(arg2, res2)) => arg1
                .find_substitution(arg2)
                .compose(&res1.find_substitution(res2)),
            (Type::Polymorphic(var), _) => {
                let mut subst = Substitution::new();
                if !var.1.is_empty() {
                    subst.insert(var.clone(), other.clone());
                }
                subst
            }
            _ => Substitution::new()
        }
    }

    /// Turns a function type into a vector of the argument types and the return type
    pub fn unfold(&self) -> Vec<Self> {
        match &self.content {
            Type::Function(a, b) => {
                let mut vec = vec![a.as_ref().clone()];
                vec.append(&mut b.unfold());
                vec
            }
            _ => vec![self.clone()]
        }
    }

    pub fn generalize(&self, env: &Environment<'a>) -> Scheme<'a> {
        Scheme {
            vars: self
                .free_vars()
                .difference(&env.free_vars())
                .cloned()
                .collect(),
            inner: self.clone(),
        }
    }
}

impl fmt::Display for Type<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.format(&HashMap::new()))
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub enum TypeClass {
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
            TypeClass::Show => write!(f, "Show"),
            TypeClass::Eq => write!(f, "Eq"),
            TypeClass::Ord => write!(f, "Ord")
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Hash, Ord, PartialOrd)]
pub struct Scheme<'a> {
    pub vars: BTreeSet<TypeVariable>,
    pub inner: PType<'a>,
}

impl<'a> Scheme<'a> {
    pub fn instantiate(&self, gen: &mut Generator) -> PType<'a> {
        let subst = self.vars
            .iter()
            .map(|var| {
                let t = Type::Polymorphic(gen.fresh_with(var.1.clone()));
                (var.clone(), self.inner.with(t))
            })
            .collect();
        self.inner.apply(&subst)
    }
}

impl<'a> From<PType<'a>> for Scheme<'a> {
    fn from(inner: PType<'a>) -> Self {
        Scheme {
            vars: BTreeSet::new(),
            inner,
        }
    }
}

impl fmt::Display for Scheme<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let poly_names: HashMap<TypeVariable, char> = self.vars
            .iter()
            .cloned()
            .zip('a'..'z')
            .collect();
        let mut type_classes: Vec<String> = self.vars
            .iter()
            .cloned()
            .filter(|var| !var.1.is_empty())
            .flat_map(|var| {
                let poly_names = &poly_names;
                var.1
                    .clone()
                    .into_iter()
                    .map(move |class|
                        format!("{} {}", class, poly_names.get(&var).unwrap())
                    )
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
pub struct Environment<'a>(HashMap<(Id, Space), Scheme<'a>>);

impl Environment<'_> {
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
            let fun_type = Type::parse_function(&mut annotation
                .tokenize()
                .unwrap()
                .peekable(), &mut Generator::new(), &mut HashMap::new(),
            ).unwrap();
            let scheme = fun_type.generalize(&mut env);
            env.insert((Id(name.to_owned()), Space::Fun), scheme);
        }
        env
    }
}

impl<'a> Deref for Environment<'a> {
    type Target = HashMap<(Id, Space), Scheme<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Environment<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct Substitution<'a>(BTreeMap<TypeVariable, PType<'a>>);

impl<'a> Substitution<'a> {
    pub fn new() -> Self {
        Substitution(BTreeMap::new())
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

    pub fn apply(&mut self, subst: &Substitution<'a>) {
        self.0 = self.0
            .iter()
            .map(|(var, t)| (var.clone(), t.apply(subst)))
            .collect();
    }
}

impl<'a> Deref for Substitution<'a> {
    type Target = BTreeMap<TypeVariable, PType<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for Substitution<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<'a> FromIterator<(TypeVariable, PType<'a>)> for Substitution<'a> {
    fn from_iter<T: IntoIterator<Item=(TypeVariable, PType<'a>)>>(iter: T) -> Self {
        Substitution(iter.into_iter().collect())
    }
}

pub trait Typed<'a> {
    fn free_vars(&self) -> HashSet<TypeVariable>;

    fn apply(&self, subst: &Substitution<'a>) -> Self;
}

impl<'a> Typed<'a> for PType<'a> {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        match &self.content {
            Type::Void | Type::Int | Type::Bool | Type::Char => HashSet::new(),
            Type::Tuple(l, r) => l
                .free_vars()
                .union(&r.free_vars())
                .cloned()
                .collect(),
            Type::List(a) => a.free_vars(),
            Type::Function(a, b) => a
                .free_vars()
                .union(&b.free_vars())
                .cloned()
                .collect(),
            Type::Polymorphic(v) => Some(v.clone()).into_iter().collect(),
        }
    }

    fn apply(&self, subst: &Substitution<'a>) -> Self {
        match &self.content {
            Type::Void | Type::Int | Type::Bool | Type::Char => self.clone(),
            Type::Tuple(l, r) => self
                .with(Type::Tuple(Box::new(l.apply(subst)), Box::new(r.apply(subst)))),
            Type::List(a) => self
                .with(Type::List(Box::new(a.apply(subst)))),
            Type::Function(a, b) => self
                .with(Type::Function(Box::new(a.apply(subst)), Box::new(b.apply(subst)))),
            Type::Polymorphic(v) => subst.get(v).unwrap_or(self).clone(),
        }
    }
}

impl<'a, T: Typed<'a>> Typed<'a> for Vec<T> {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self
            .iter()
            .flat_map(|t| t.free_vars())
            .collect()
    }

    fn apply(&self, subst: &Substitution<'a>) -> Self {
        self
            .iter()
            .map(|t| t.apply(&subst))
            .collect()
    }
}

impl<'a> Typed<'a> for Scheme<'a> {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self.inner
            .free_vars()
            .difference(&self.vars.iter().cloned().collect())
            .cloned()
            .collect()
    }

    fn apply(&self, subst: &Substitution<'a>) -> Self {
        Scheme {
            vars: self.vars.clone(),
            inner: self.inner
                .apply(&Substitution(subst
                    .iter()
                    .filter(|&(t, _)| !self.vars.contains(t))
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect())),
        }
    }
}

impl<'a> Typed<'a> for Environment<'a> {
    fn free_vars(&self) -> HashSet<TypeVariable> {
        self
            .values()
            .flat_map(|t| t.free_vars())
            .collect()
    }

    fn apply(&self, subst: &Substitution<'a>) -> Self {
        Environment(self
            .iter()
            .map(|(k, v)| (k.clone(), v.apply(subst)))
            .collect()
        )
    }
}
