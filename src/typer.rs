use error::Result;

use crate::algorithm_w::{Environment, Generator, Space, Substitution, Type, Typed};
use crate::call_graph;
use crate::lexer::Field;
use crate::tree::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
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

impl InferMut for SPL {
    fn infer_type_mut(&self, env: &mut Environment, gen: &mut Generator) -> Result<Type> {
        // TODO: Check for duplicate definitions
        let sccs = call_graph::topsorted_sccs(self).ok_or(TypeError::Conflict(Id("Some".to_owned())))?;
        // TODO: Check variable cycles

        for scc in sccs {
            // First add all members of this scc to the environment
            for decl in &scc {
                match decl {
                    Decl::VarDecl(decl) => {
                        if env.insert((decl.id.clone(), Space::Var), decl.var_type.transform(gen).into()).is_some() {
                            return Err(TypeError::Conflict(decl.id.clone()));
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
                            return Err(TypeError::Conflict(decl.id.clone()));
                        }
                    }
                };
            }

            // Then infer their types
            for decl in &scc {
                let (subst, _) = decl.infer_type(env, gen)?;
                *env = env.apply(&subst);
            }

            // And finally generalize them, so their type does change anymore
            for decl in &scc {
                if let Decl::FunDecl(decl) = decl {
                    let old = env.remove(&(decl.id.clone(), Space::Fun)).unwrap();
                    let new = old.inner.generalize(env);
                    env.insert((decl.id.clone(), Space::Fun), new);
                }
            }
        }

        Ok(Type::Void)
    }
}

impl Infer for Decl {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer_type(env, gen),
            Decl::FunDecl(fun_decl) => fun_decl.infer_type(env, gen)
        }
    }
}

impl Infer for VarDecl {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        // Infer new type
        let (subst_i, inferred) = self.exp.infer_type(env, gen)?;

        // TODO: Necessary?
        let env = &env.apply(&subst_i);

        // Get current type
        let var_type = env
            .get(&(self.id.clone(), Space::Var))
            .ok_or(TypeError::Unbound(self.id.clone()))?.inner
            .clone();

        // Check if new type is compatible with old type
        let subst_u = var_type.unify_with(&inferred)?;

        Ok((subst_u.compose(&subst_i), Type::Void))
    }
}

impl Infer for FunDecl {
    fn infer_type(&self, env: &Environment, gen: &mut Generator) -> Result<(Substitution, Type)> {
        // TODO: check for doubly defined arguments and variables

        // Create local scope
        let mut env = env.clone();

        // Get current type
        let mut arg_types = env
            .get(&(self.id.clone(), Space::Fun))
            .ok_or(TypeError::Unbound(self.id.clone()))?.inner
            .unfold();
        let ret_type = arg_types.pop().unwrap();

        // Add arguments to local scope
        env.extend(self.args
            .iter()
            .cloned()
            .map(|id| (id, Space::Var))
            .zip(arg_types
                .into_iter()
                .map(|arg| arg.into())));

        // Add variable declarations to local scope
        let subst_v = self.var_decls
            .iter()
            .fold(Ok(Substitution::new()), |acc, decl| {
                let subst_a = acc?;
                env.insert((decl.id.clone(), Space::Var), decl.var_type.transform(gen).into());
                let (subst_i, _) = decl.infer_type(&env, gen)?;
                env = env.apply(&subst_i);
                Ok(subst_i.compose(&subst_a))
            })?;

        // Infer types in inner statements
        let (subst_i, result) = self.stmts.try_infer_type(&env, gen)?;

        // Check return type
        let (inferred, complete) = result.unwrap_or((Type::Void, true));
        if !complete && inferred != Type::Void {
            return Err(TypeError::Incomplete(self.id.clone()));
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
                let env = &env.apply(&subst_i);

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
                Some(t) => Ok((Substitution::new(), t.inner.clone()))
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
                env = env.apply(&subst_i);
                types.push(inferred);
                Ok(subst_i.compose(&subst_a))
            })?;

        types.apply(&subst_i);
        // TODO: Necessary? Probably
        arg_types.apply(&subst_i);

        let subst_u = types
            .into_iter()
            .zip(&arg_types)
            .fold(Ok(Substitution::new()), |acc, (inferred, required)| {
                let subst = acc?;
                let subst_u = required.apply(&subst).unify_with(&inferred)?;
                Ok(subst_u.compose(&subst))
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

    use crate::algorithm_w::{Type, TypeVariable};
    use crate::tree::Id;

    pub type Result<T, E = TypeError> = std::result::Result<T, E>;

    #[derive(Eq, PartialEq)]
    pub enum TypeError {
        Mismatch {
            expected: Type,
            found: Type,
        },
        TypeClass {
            found: Type,
            class: Id,
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
