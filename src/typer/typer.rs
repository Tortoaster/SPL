use std::collections::HashSet;

use error::Result;

use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, PExp, PStmt, SPL, Stmt, VarDecl};
use crate::position::Join;
use crate::typer::{Environment, Generator, PType, Space, Substitution, Type, Typed};
use crate::typer::call_graph;
use crate::typer::error::TypeError;

pub trait Infer<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)>;
}

pub trait TryInfer<'a> {
    fn try_infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, Option<(PType<'a>, bool)>)>;
}

impl<'a> SPL<'a> {
    pub fn infer_types(&mut self, env: &mut Environment<'a>, gen: &mut Generator) -> Result<'a, ()> {
        // Check for duplicate functions
        let mut names = HashSet::new();
        for decl in &self.decls {
            if let Decl::FunDecl(fun_decl) = &decl.content {
                let id = &fun_decl.id.content;
                if !names.insert(id.clone()) {
                    return Err(decl.with(TypeError::FunConflict(id.clone())));
                }
            }
        }

        // Create dependency graph
        let sccs = call_graph::topsorted_sccs(&self);

        // Detect cyclic variable definitions
        for scc in &sccs {
            let vars: Vec<&VarDecl> = scc
                .into_iter()
                .filter_map(|decl| if let Decl::VarDecl(var_decl) = &decl.content {
                    Some(var_decl)
                } else {
                    None
                })
                .collect();
            if vars.len() > 1 {
                let pos = vars[0].id.clone().extend(&vars[1].id);
                return Err(pos.with(TypeError::Codependent(vars[0].id.content.clone(), vars[1].id.content.clone())));
            }
        }

        // Type all declarations in the right order
        for scc in &sccs {
            // First add all members of this scc to the environment
            for decl in scc {
                let inner = match &decl.content {
                    Decl::VarDecl(decl) => {
                        let var_type = decl.var_type.borrow();
                        match &var_type.content {
                            None => var_type.with(Type::Polymorphic(gen.fresh())),
                            Some(var_type) => var_type.generalize(env).instantiate(gen)
                        }
                    }
                    Decl::FunDecl(decl) => {
                        let fun_type = decl.fun_type.borrow();
                        match &fun_type.content {
                            None => {
                                let args: Vec<PType> = std::iter::repeat_with(||
                                    fun_type.with(Type::Polymorphic(gen.fresh()))
                                )
                                    .take(decl.args.len())
                                    .collect();
                                args
                                    .into_iter()
                                    .rfold(fun_type.with(Type::Polymorphic(gen.fresh())), |res, arg|
                                        res
                                            .with(())
                                            .extend(&arg)
                                            .with(Type::Function(Box::new(arg), Box::new(res))),
                                    )
                            }
                            Some(fun_type) => fun_type.clone()
                        }
                    }
                };
                if env.insert((decl.id(), decl.space()), inner.into()).is_some() {
                    return Err(decl.with(TypeError::VarConflict(decl.id())));
                }
            }

            // Then infer their types
            let mut subst = Substitution::new();
            for decl in scc {
                let (s, _) = decl.infer(env, gen)?;
                *env = env.apply(&s);
                subst = subst.compose(&s);
            }

            // Generalize them, so their type does not change anymore
            for decl in scc {
                if let Decl::FunDecl(decl) = &decl.content {
                    let old = env.remove(&(decl.id.content.clone(), Space::Fun)).unwrap();
                    let new = old.inner.generalize(env);
                    env.insert((decl.id.content.clone(), Space::Fun), new);
                }
            }

            // Update their types in the tree
            for decl in scc {
                match &decl.content {
                    Decl::VarDecl(var_decl) => {
                        let t = env.get(&(var_decl.id.content.clone(), Space::Var)).unwrap();
                        var_decl.var_type.borrow_mut().content.replace(t.inner.clone());
                    }
                    Decl::FunDecl(fun_decl) => {
                        let t = env.get(&(fun_decl.id.content.clone(), Space::Fun)).unwrap();
                        fun_decl.fun_type.borrow_mut().content.replace(t.inner.clone());
                    }
                }
            }

            // Update function call type arguments with most recent substitution
            for decl in scc {
                match &decl.content {
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

        // Sort declarations in topological order
        let mut sorted_decls = self.decls.clone();
        sorted_decls.sort_by(|a, b| sccs
            .iter()
            .position(|d| d.contains(&a))
            .cmp(&sccs.iter().position(|d| d.contains(&b))));
        self.decls = sorted_decls;

        Ok(())
    }
}

impl<'a> Exp<'a> {
    fn update_fun_calls(&self, subst: &Substitution<'a>) {
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

impl<'a> Stmt<'a> {
    fn update_fun_calls(&self, subst: &Substitution<'a>) {
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

impl<'a> Infer<'a> for Decl<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)> {
        match self {
            Decl::VarDecl(var_decl) => var_decl.infer(env, gen),
            Decl::FunDecl(fun_decl) => fun_decl.infer(env, gen)
        }
    }
}

impl<'a> Infer<'a> for VarDecl<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)> {
        // Infer new type
        let (subst_i, inferred) = self.exp.infer(env, gen)?;

        let env = &env.apply(&subst_i);

        // Get current type
        let var_type = env
            .get(&(self.id.content.clone(), Space::Var))
            .ok_or(self.var_type.borrow().with(TypeError::Unbound(self.id.content.clone())))?.inner
            .clone();

        // Check if new type is compatible with old type
        let subst_u = var_type.unify_with(&inferred)?;

        Ok((subst_u.compose(&subst_i), self.id.with(Type::Void)))
    }
}

impl<'a> Infer<'a> for FunDecl<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)> {
        // Check for double defined arguments
        let mut names = HashSet::new();
        for id in &self.args {
            if !names.insert(id.content.clone()) {
                return Err(id.with(TypeError::VarConflict(id.content.clone())));
            }
        }

        // Check for doubly defined variables
        let mut names = HashSet::new();
        for var_decl in &self.var_decls {
            if !names.insert(var_decl.id.content.clone()) {
                return Err(var_decl.with(TypeError::VarConflict(var_decl.id.content.clone())));
            }
        }

        // Create local scope
        let mut env = env.clone();

        // Get current type
        let mut arg_types = env
            .get(&(self.id.content.clone(), Space::Fun))
            .ok_or(self.id.with(TypeError::Unbound(self.id.content.clone())))?.inner
            .unfold();
        let ret_type = arg_types.pop().unwrap();

        // Add arguments to local scope
        env.extend(self.args
            .iter()
            .cloned()
            .map(|id| (id.content, Space::Var))
            .zip(arg_types
                .into_iter()
                .map(|arg| arg.into())));

        // Add variable declarations to local scope
        let subst_v = self.var_decls
            .iter()
            .fold(Ok(Substitution::new()), |acc, decl| {
                let subst_a = acc?;
                let var_type = decl.var_type.borrow();
                let inner = match &var_type.content {
                    None => var_type.with(Type::Polymorphic(gen.fresh())),
                    Some(var_type) => var_type.generalize(&env).instantiate(gen)
                };
                env.insert((decl.id.content.clone(), Space::Var), inner.into());
                let (subst_i, _) = decl.infer(&env, gen)?;
                env = env.apply(&subst_i);
                Ok(subst_i.compose(&subst_a))
            })?;

        // Infer types in inner statements
        let (subst_i, result) = self.stmts.try_infer(&env, gen)?;

        // Check return type
        let inferred = match result {
            None => Type::Void,
            Some((inferred, complete)) => {
                if !complete && inferred.content != Type::Void {
                    return Err(self.stmts
                        .join_with(TypeError::Incomplete(self.id.content.clone()))
                        .unwrap_or(self.id
                            .with(TypeError::Incomplete(self.id.content.clone()))
                        )
                    );
                }
                inferred.content
            }
        };
        let subst_r = ret_type.unify_with(&ret_type.with(inferred))?;

        Ok((subst_r.compose(&subst_i.compose(&subst_v)), self.id.with(Type::Void)))
    }
}

trait Combine<'a> {
    fn combine_with(&self, other: &Self, both: bool) -> Result<'a, (Substitution<'a>, Option<(PType<'a>, bool)>)>;
}

impl<'a> Combine<'a> for Option<(PType<'a>, bool)> {
    fn combine_with(&self, other: &Self, both: bool) -> Result<'a, (Substitution<'a>, Option<(PType<'a>, bool)>)> {
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

impl<'a> TryInfer<'a> for Vec<PStmt<'a>> {
    fn try_infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, Option<(PType<'a>, bool)>)> {
        let mut env = env.clone();
        let mut current: Option<(PType, bool)> = None;

        let subst = self
            .iter()
            .fold(Ok(Substitution::new()), |acc, stmt| {
                let subst_a = acc?;
                let (subst_i, result) = stmt.try_infer(&env, gen)?;
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

impl<'a> TryInfer<'a> for PStmt<'a> {
    fn try_infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, Option<(PType<'a>, bool)>)> {
        match &self.content {
            Stmt::If(c, t, e) => {
                let (subst_i, inferred) = c.infer(env, gen)?;
                let subst_u = inferred.unify_with(&c.with(Type::Bool))?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer(env, gen)?;
                let env = &env.apply(&subst_t);

                let (subst_e, ret_e) = e.try_infer(env, gen)?;

                let (subst_r, mut ret_type) = ret_t.combine_with(&ret_e, true)?;

                let subst = subst_r.compose(&subst_e.compose(&subst_t.compose(&subst)));

                if let Some((t, b)) = &ret_type {
                    ret_type = Some((t.apply(&subst), *b));
                }

                Ok((subst, ret_type))
            }
            Stmt::While(c, t) => {
                let (subst_i, inferred) = c.infer(env, gen)?;
                let subst_u = inferred.unify_with(&c.with(Type::Bool))?;
                let subst = subst_u.compose(&subst_i);
                let env = &env.apply(&subst);

                let (subst_t, ret_t) = t.try_infer(env, gen)?;

                let subst = subst_t.compose(&subst);
                let ret_type = ret_t.map(|(t, _)| (t.apply(&subst), false));

                Ok((subst, ret_type))
            }
            Stmt::Assignment(x, f, e) => {
                let (subst_i, inferred) = e.infer(env, gen)?;

                let env = &env.apply(&subst_i);

                let remembered = env
                    .get(&(x.content.clone(), Space::Var))
                    .ok_or(x.with(TypeError::Unbound(x.content.clone())))?.inner
                    .clone();

                let mut current = remembered;
                let subst_f = f
                    .iter()
                    .fold(Ok(Substitution::new()), |acc, field| {
                        let subst = acc?;
                        let inner = e.with(Type::Polymorphic(gen.fresh()));
                        match field.content {
                            Field::Head => {
                                let thing = current.with(Type::List(Box::new(inner.clone())));
                                let subst_u = thing.unify_with(&current)?;
                                current = inner.apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::Tail => {
                                let thing = current.with(Type::List(Box::new(inner.clone())));
                                let subst_u = thing.unify_with(&current)?;
                                current = current.with(Type::List(Box::new(inner))).apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::First => {
                                let thing = current.with(Type::Tuple(Box::new(inner.clone()), Box::new(current.with(Type::Polymorphic(gen.fresh())))));
                                let subst_u = thing.unify_with(&current)?;
                                current = inner.apply(&subst_u);
                                Ok(subst_u.compose(&subst))
                            }
                            Field::Second => {
                                let thing = current.with(Type::Tuple(Box::new(current.with(Type::Polymorphic(gen.fresh()))), Box::new(inner.clone())));
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
                let (subst, _) = fun_call.infer(env, gen)?;
                Ok((subst, None))
            }
            Stmt::Return(e) => match e {
                None => Ok((Substitution::new(), Some((self.with(Type::Void), true)))),
                Some(exp) => {
                    let (subst, inferred) = exp.infer(env, gen)?;
                    Ok((subst, Some((inferred, true))))
                }
            }
        }
    }
}

impl<'a> Infer<'a> for PExp<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)> {
        match &self.content {
            Exp::Variable(id) => match env.get(&(id.clone(), Space::Var)) {
                None => Err(self.with(TypeError::Unbound(id.clone()))),
                Some(t) => Ok((Substitution::new(), t.inner.clone()))
            }
            Exp::Number(_) => Ok((Substitution::new(), self.with(Type::Int))),
            Exp::Character(_) => Ok((Substitution::new(), self.with(Type::Char))),
            Exp::Boolean(_) => Ok((Substitution::new(), self.with(Type::Bool))),
            Exp::FunCall(fun_call) => fun_call.infer(env, gen),
            Exp::Nil => Ok((Substitution::new(), self.with(Type::List(Box::new(self.with(Type::Polymorphic(gen.fresh()))))))),
            Exp::Tuple(l, r) => {
                let (l_subst, l_inferred) = l.infer(env, gen)?;
                let (r_subst, r_inferred) = r.infer(&env.apply(&l_subst), gen)?;
                let subst = r_subst.compose(&l_subst);
                let l_inferred = l.with(l_inferred).apply(&subst);
                Ok((subst, self.with(Type::Tuple(Box::new(l_inferred), Box::new(r_inferred)))))
            }
        }
    }
}

impl<'a> Infer<'a> for FunCall<'a> {
    fn infer(&self, env: &Environment<'a>, gen: &mut Generator) -> Result<'a, (Substitution<'a>, PType<'a>)> {
        // Get required type
        let function = env
            .get(&(self.id.content.clone(), Space::Fun))
            .ok_or(self.id.with(TypeError::Unbound(self.id.content.clone())))?;

        let mut arg_types = function
            .instantiate(gen)
            .unfold();
        let ret_type = arg_types
            .pop()
            .unwrap();

        // Check number of arguments
        let required = arg_types.len();
        let got = self.args.len();
        if got != required {
            let function = self.id.content.clone();
            return Err(self.id.with(TypeError::ArgumentNumber { function, required, got }));
        }

        // Infer arguments
        let mut env = env.clone();
        let mut types = Vec::new();
        let subst_i = self.args
            .iter()
            .fold(Ok(Substitution::new()), |acc, exp| {
                let subst = acc?;
                let (subst_i, inferred) = exp.infer(&env, gen)?;
                env = env.apply(&subst_i);
                types.push(inferred);
                Ok(subst_i.compose(&subst))
            })?;

        types.apply(&subst_i);
        arg_types.apply(&subst_i);

        // Check if arguments are the right type
        arg_types
            .iter()
            .zip(&types)
            .map(|(arg, inferred)| inferred.unify_with(arg))
            .collect::<Result<Vec<Substitution>>>()?;

        // Update function type
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
            .rfold(t.clone(), |acc, t| acc
                .with(())
                .extend(&t)
                .with(Type::Function(Box::new(t), Box::new(acc))),
            );

        // Annotate function call with type
        *self.type_args.borrow_mut() = function.inner.find_substitution(&full_type);

        Ok((subst, t))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::parser::Id;
    use crate::position::Pos;
    use crate::typer::{Type, TypeClass, TypeVariable};

    pub type Result<'a, T, E = Pos<'a, TypeError<'a>>> = std::result::Result<T, E>;

    #[derive(Eq, PartialEq)]
    pub enum TypeError<'a> {
        Mismatch {
            expected: Type<'a>,
            found: Type<'a>,
        },
        TypeClass {
            found: Type<'a>,
            class: TypeClass,
        },
        Unbound(Id),
        FunConflict(Id),
        VarConflict(Id),
        Recursive(TypeVariable, Type<'a>),
        Incomplete(Id),
        ArgumentNumber {
            function: Id,
            required: usize,
            got: usize,
        },
        Codependent(Id, Id),
        // UndefinedClass(TypeClass),
    }

    impl fmt::Display for TypeError<'_> {
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
                    write!(f, "Occur check fails: {:?} occurs in {:?}", v, t),
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

    impl Debug for TypeError<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for TypeError<'_> {}
}
