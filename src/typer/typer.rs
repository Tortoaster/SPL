use std::collections::HashSet;

use error::Result;

use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, PStmt, SPL, Stmt, VarDecl};
use crate::typer::{Environment, Generator, Space, Substitution, Type, Typed};
use crate::typer::call_graph;
use crate::typer::error::TypeError;

pub trait Infer {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)>;
}

pub trait InferMut {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type>;
}

pub trait TryInfer {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<(Type, bool)>)>;
}

impl<'a> SPL<'a> {
    pub fn infer_types(&mut self, env: &mut Environment, gen: &mut Generator) -> Result<()> {
        // Check for duplicate functions
        let mut names = HashSet::new();
        for decl in &self.decls {
            if let Decl::FunDecl(fun_decl) = &decl.inner {
                let id = &fun_decl.id.inner;
                if !names.insert(id.clone()) {
                    return Err(TypeError::FunConflict(id.clone()));
                }
            }
        }

        // Create dependency graph
        let sccs = call_graph::topsorted_sccs(&self);

        // Detect cyclic variable definitions
        for scc in &sccs {
            let vars: Vec<&VarDecl> = scc
                .into_iter()
                .filter_map(|decl| if let Decl::VarDecl(var_decl) = decl {
                    Some(var_decl)
                } else {
                    None
                })
                .collect();
            if vars.len() > 1 {
                return Err(TypeError::Codependent(vars[0].id.inner.clone(), vars[1].id.inner.clone()))
            }
        }

        // Type all declarations in the right order
        for scc in sccs {
            // First add all members of this scc to the environment
            for decl in &scc {
                let inner = match decl {
                    Decl::VarDecl(decl) => match &decl.var_type.borrow().inner {
                        None => Type::Polymorphic(gen.fresh()),
                        Some(var_type) => var_type.generalize(env).instantiate(gen)
                    },
                    Decl::FunDecl(decl) => match &decl.fun_type.borrow().inner {
                        None => {
                            let args: Vec<Type> = std::iter::repeat_with(|| Type::Polymorphic(gen.fresh()))
                                .take(decl.args.len())
                                .collect();
                            args
                                .into_iter()
                                .rfold(Type::Polymorphic(gen.fresh()), |res, arg| Type::Function(Box::new(arg), Box::new(res)))
                        }
                        Some(fun_type) => fun_type.instantiate(gen)
                    }
                };
                if env.insert((decl.id(), decl.space()), inner.into()).is_some() {
                    return Err(TypeError::VarConflict(decl.id()));
                }
            }

            // Then infer their types
            let mut subst = Substitution::new();
            for decl in &scc {
                let (s, _) = decl.infer_type(env, gen)?;
                *env = env.apply(&s);
                subst = subst.compose(&s);
            }

            // Generalize them, so their type does change anymore
            for decl in &scc {
                if let Decl::FunDecl(decl) = decl {
                    let old = env.remove(&(decl.id.inner.clone(), Space::Fun)).unwrap();
                    let new = old.inner.generalize(env);
                    env.insert((decl.id.inner.clone(), Space::Fun), new);
                }
            }

            // Update their types in the tree
            for decl in &scc {
                match decl {
                    Decl::VarDecl(var_decl) => {
                        let t = env.get(&(var_decl.id.inner.clone(), Space::Var)).unwrap();
                        var_decl.var_type.borrow_mut().inner.replace(t.inner.clone());
                    }
                    Decl::FunDecl(fun_decl) => {
                        let t = env.get(&(fun_decl.id.inner.clone(), Space::Fun)).unwrap();
                        fun_decl.fun_type.borrow_mut().inner.replace(t.clone());
                    }
                }
            }

            // Update function call type arguments with most recent substitution
            for decl in &scc {
                match decl {
                    Decl::VarDecl(var_decl) => var_decl.exp.update_fun_calls(&subst),
                    Decl::FunDecl(fun_decl) => {
                        for var_decl in &fun_decl.var_decls {
                            var_decl.exp.update_fun_calls(&subst);
                        }
                        for stmt in &fun_decl.stmts {
                            stmt.update_fun_calls(&subst)
                        }
                    }
                }
            }
        }

        // TODO: sort decls

        Ok(())
    }
}

impl Exp<'_> {
    fn update_fun_calls(&self, subst: &Substitution) {
        match self {
            Exp::Variable(_) | Exp::Number(_) | Exp::Character(_) | Exp::Boolean(_) | Exp::Nil => {}
            Exp::FunCall(fun_call) => fun_call.type_args.borrow_mut().apply(subst),
            Exp::Tuple(l, r) => {
                l.update_fun_calls(subst);
                r.update_fun_calls(subst);
            }
        }
    }
}

impl Stmt<'_> {
    fn update_fun_calls(&self, subst: &Substitution) {
        match self {
            Stmt::If(e, t, o) => {
                e.update_fun_calls(subst);
                for stmt in t.into_iter().chain(o) {
                    stmt.update_fun_calls(&subst);
                }
            }
            Stmt::While(e, t) => {
                e.update_fun_calls(subst);
                for stmt in t {
                    stmt.update_fun_calls(&subst);
                }
            }
            Stmt::Assignment(_, _, e) => e.update_fun_calls(subst),
            Stmt::FunCall(fun_call) => fun_call.type_args.borrow_mut().apply(subst),
            Stmt::Return(ret) => if let Some(e) = ret {
                e.update_fun_calls(subst);
            }
        }
    }
}

impl Infer for Decl<'_> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer_type(env, gen),
            Decl::FunDecl(fun_decl) => fun_decl.infer_type(env, gen)
        }
    }
}

impl Infer for VarDecl<'_> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        // Infer new type
        let (subst_i, inferred) = self.exp.infer_type(env, gen)?;

        let env = &env.apply(&subst_i);

        // Get current type
        let var_type = env
            .get(&(self.id.inner.clone(), Space::Var))
            .ok_or(TypeError::Unbound(self.id.inner.clone()))?.inner
            .clone();

        // Check if new type is compatible with old type
        let subst_u = var_type.unify_with(&inferred)?;

        Ok((subst_u.compose(&subst_i), Type::Void))
    }
}

impl Infer for FunDecl<'_> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        // Check for double defined arguments
        let mut names = HashSet::new();
        for id in &self.args {
            if !names.insert(id.inner.clone()) {
                return Err(TypeError::VarConflict(id.inner.clone()));
            }
        }

        // Check for double defined variables
        let mut names = HashSet::new();
        for var_decl in &self.var_decls {
            if !names.insert(var_decl.id.inner.clone()) {
                return Err(TypeError::VarConflict(var_decl.id.inner.clone()));
            }
        }

        // Create local scope
        let mut env = env.clone();

        // Get current type
        let mut arg_types = env
            .get(&(self.id.inner.clone(), Space::Fun))
            .ok_or(TypeError::Unbound(self.id.inner.clone()))?.inner
            .unfold();
        let ret_type = arg_types.pop().unwrap();

        // Add arguments to local scope
        env.extend(self.args
            .iter()
            .cloned()
            .map(|id| (id.inner, Space::Var))
            .zip(arg_types
                .into_iter()
                .map(|arg| arg.into())));

        // Add variable declarations to local scope
        let subst_v = self.var_decls
            .iter()
            .fold(Ok(Substitution::new()), |acc, decl| {
                let subst_a = acc?;
                let inner = match &decl.var_type.borrow().inner {
                    None => Type::Polymorphic(gen.fresh()),
                    Some(var_type) => var_type.generalize(&env).instantiate(gen)
                };
                env.insert((decl.id.inner.clone(), Space::Var), inner.into());
                let (subst_i, _) = decl.infer_type(&env, gen)?;
                env = env.apply(&subst_i);
                Ok(subst_i.compose(&subst_a))
            })?;

        // Infer types in inner statements
        let (subst_i, result) = self.stmts.try_infer_type(&env, gen)?;

        // Check return type
        let (inferred, complete) = result.unwrap_or((Type::Void, true));
        if !complete && inferred != Type::Void {
            return Err(TypeError::Incomplete(self.id.inner.clone()));
        }
        let subst_r = ret_type.unify_with(&inferred)?;

        Ok((subst_r.compose(&subst_i.compose(&subst_v)), Type::Void))
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

impl TryInfer for Vec<PStmt<'_>> {
    fn try_infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Option<(Type, bool)>)> {
        let mut env = env.clone();
        let mut current: Option<(Type, bool)> = None;

        let subst = self
            .iter()
            .fold(Ok(Substitution::new()), |acc, stmt| {
                let subst_a = acc?;
                let (subst_i, result) = stmt.try_infer_type(&env, gen)?;
                let (subst_u, new) = current.combine_with(&result, false)?;
                let subst = subst_u.compose(&subst_i);
                env = env.apply(&subst);

                current = new;
                if let Some((t, b)) = &current {
                    current = Some((t.apply(&subst), *b));
                }

                Ok(subst.compose(&subst_a))
            })?;

        Ok((subst, current))
    }
}

impl TryInfer for Stmt<'_> {
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
                let ret_type = ret_t.map(|(t, _)| (t.apply(&subst), false));

                Ok((subst, ret_type))
            }
            Stmt::Assignment(x, f, e) => {
                let (subst_i, inferred) = e.infer_type(env, gen)?;

                let env = &env.apply(&subst_i);

                let remembered = env
                    .get(&(x.inner.clone(), Space::Var))
                    .ok_or(TypeError::Unbound(x.inner.clone()))?.inner
                    .clone();

                let mut current = remembered;
                let subst_f = f
                    .iter()
                    .fold(Ok(Substitution::new()), |acc, field| {
                        let subst = acc?;
                        let inner = Type::Polymorphic(gen.fresh());
                        match field.inner {
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

impl Infer for Exp<'_> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Exp::Variable(id) => match env.get(&(id.clone(), Space::Var)) {
                None => Err(TypeError::Unbound(id.clone())),
                Some(t) => Ok((Substitution::new(), t.inner.clone()))
            }
            Exp::Number(_) => Ok((Substitution::new(), Type::Int)),
            Exp::Character(_) => Ok((Substitution::new(), Type::Char)),
            Exp::Boolean(_) => Ok((Substitution::new(), Type::Bool)),
            Exp::FunCall(fun_call) => fun_call.infer_type(env, gen),
            Exp::Nil => Ok((Substitution::new(), Type::Array(Box::new(Type::Polymorphic(gen.fresh()))))),
            Exp::Tuple(l, r) => {
                let (l_subst, l_inferred) = l.infer_type(env, gen)?;
                let (r_subst, r_inferred) = r.infer_type(&env.apply(&l_subst), gen)?;
                let subst = r_subst.compose(&l_subst);
                let l_inferred = l_inferred.apply(&subst);
                Ok((subst, Type::Tuple(Box::new(l_inferred), Box::new(r_inferred))))
            }
        }
    }
}

impl Infer for FunCall<'_> {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        let function = env
            .get(&(self.id.inner.clone(), Space::Fun))
            .ok_or(TypeError::Unbound(self.id.inner.clone()))?;

        let mut arg_types = function
            .instantiate(gen)
            .unfold();

        let ret_type = arg_types
            .pop()
            .unwrap();

        let id = self.id.inner.clone();
        let required = arg_types.len();
        let got = self.args.len();
        if required != got {
            return Err(TypeError::ArgumentNumber { function: id, required, got });
        }

        let mut env = env.clone();
        let mut types = Vec::new();
        let subst_i = self.args
            .iter()
            .fold(Ok(Substitution::new()), |acc, exp| {
                let subst = acc?;
                let (subst_i, inferred) = exp.infer_type(&env, gen)?;
                env = env.apply(&subst_i);
                types.push(inferred);
                Ok(subst_i.compose(&subst))
            })?;

        types.apply(&subst_i);
        arg_types.apply(&subst_i);

        let subst_u = types
            .iter()
            .zip(&arg_types)
            .fold(Ok(Substitution::new()), |acc, (inferred, required)| {
                let subst = acc?;
                let subst_u = required.apply(&subst).unify_with(inferred)?;
                Ok(subst_u.compose(&subst))
            })?;

        let subst = subst_u.compose(&subst_i);
        types = types.apply(&subst);
        let t = ret_type.apply(&subst);

        // Decorate function call with filled-in type arguments
        let full_type = types
            .into_iter()
            .rfold(t.clone(), |acc, t| Type::Function(Box::new(t), Box::new(acc)));

        *self.type_args.borrow_mut() = function.inner.find_substitution(&full_type);

        Ok((subst, t))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::parser::Id;
    use crate::typer::{Type, TypeClass, TypeVariable};

    pub type Result<T, E = TypeError> = std::result::Result<T, E>;

    #[derive(Eq, PartialEq)]
    pub enum TypeError {
        Mismatch {
            expected: Type,
            found: Type,
        },
        TypeClass {
            found: Type,
            class: TypeClass,
        },
        Unbound(Id),
        FunConflict(Id),
        VarConflict(Id),
        Recursive(TypeVariable, Type),
        Incomplete(Id),
        ArgumentNumber {
            function: Id,
            required: usize,
            got: usize,
        },
        Codependent(Id, Id)
        // UndefinedClass(TypeClass),
    }

    impl fmt::Display for TypeError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                TypeError::Mismatch { expected, found } =>
                    write!(f, "Type mismatch: expected {}, found {}", expected, found),
                TypeError::TypeClass { found, class } =>
                    write!(f, "Type {} does not implement {}", found, class),
                TypeError::Unbound(id) =>
                    write!(f, "Unbound variable {}", id),
                TypeError::FunConflict(id) =>
                    write!(f, "Function {} is defined more than once", id),
                TypeError::VarConflict(id) =>
                    write!(f, "Variable {} is defined more than once", id),
                TypeError::Recursive(v, t) =>
                    write!(f, "Occur check fails: {:?} vs {:?}", v, t),
                TypeError::Incomplete(id) =>
                    write!(f, "Function {} does not return a correct value in all paths", id),
                TypeError::ArgumentNumber { function, got, required } =>
                    write!(f, "Function {} requires {} arguments, but {} were supplied", function, required, got),
                TypeError::Codependent(a, b) =>
                    write!(f, "Global variables {} and {} depend on each other", a, b),
                // TypeError::UndefinedClass(class) =>
                //     write!(f, "Type class {:?} not found", class),
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
