use std::collections::{HashSet, HashMap, BTreeSet};
use crate::tree::{SPL, Id, FunDecl, VarDecl, Stmt, Decl, Exp};
use crate::typer::Space;

pub struct CallGraph {
    pub fun_calls: HashMap<(Id, Space), BTreeSet<Id>>,
    pub references: HashMap<(Id, Space), BTreeSet<Id>>,
    pub assignments: HashMap<Id, BTreeSet<Id>>,
}

impl CallGraph {
    pub fn new(ast: &SPL) -> Self {
        let fun_calls = ast.decls
            .iter()
            .map(|decl| ((decl.id(), decl.space()), decl.fun_calls()))
            .collect();

        let references = ast.decls
            .iter()
            .map(|decl| ((decl.id(), decl.space()), decl.references(&HashSet::new())))
            .collect();

        let assignments = ast.decls
            .iter()
            .map(|decl| (decl.id(), decl.assignments(&HashSet::new())))
            .collect();

        CallGraph {
            fun_calls,
            references,
            assignments,
        }
    }
}

trait Calls {
    fn fun_calls(&self) -> BTreeSet<Id>;

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id>;

    fn assignments(&self, exclude: &HashSet<Id>) -> BTreeSet<Id>;
}

impl Calls for Decl {
    fn fun_calls(&self) -> BTreeSet<Id> {
        match self {
            Decl::VarDecl(decl) => decl.fun_calls(),
            Decl::FunDecl(decl) => decl.fun_calls()
        }
    }

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        match self {
            Decl::VarDecl(decl) => decl.references(&exclude),
            Decl::FunDecl(decl) => decl.references(&exclude)
        }
    }

    fn assignments(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        match self {
            Decl::VarDecl(decl) => decl.assignments(exclude),
            Decl::FunDecl(decl) => decl.assignments(exclude)
        }
    }
}

impl Calls for FunDecl {
    fn fun_calls(&self) -> BTreeSet<Id> {
        let mut calls: BTreeSet<Id> = self.var_decls
            .iter()
            .flat_map(|decl| decl.fun_calls())
            .collect();
        calls.append(&mut self.stmts
            .iter()
            .flat_map(|stmt| stmt.fun_calls())
            .collect());
        calls
    }

    fn references(&self, _: &HashSet<Id>) -> BTreeSet<Id> {
        let mut defined = HashSet::new();
        let mut refs: BTreeSet<Id> = self.var_decls
            .iter()
            .flat_map(|decl| {
                let refs = decl.references(&defined);
                defined.insert(decl.id.clone());
                refs
            })
            .collect();
        refs.append(&mut self.stmts
            .iter()
            .flat_map(|stmt| stmt.references(&defined))
            .collect());
        refs
    }

    fn assignments(&self, _: &HashSet<Id>) -> BTreeSet<Id> {
        let defined = self.var_decls
            .iter()
            .map(|decl| decl.id.clone())
            .collect();
        self.stmts
            .iter()
            .flat_map(|stmt| stmt.assignments(&defined))
            .collect()
    }
}

impl Calls for VarDecl {
    fn fun_calls(&self) -> BTreeSet<Id> {
        self.exp.fun_calls()
    }

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        self.exp.references(exclude)
    }

    fn assignments(&self, _: &HashSet<Id>) -> BTreeSet<Id> {
        // Variables cannot assign values to other variables
        BTreeSet::new()
    }
}

impl Calls for Stmt {
    fn fun_calls(&self) -> BTreeSet<Id> {
        match self {
            Stmt::If(c, t, e) => c
                .fun_calls()
                .into_iter()
                .chain(t
                    .iter()
                    .flat_map(|stmt| stmt.fun_calls())
                )
                .chain(e
                    .iter()
                    .flat_map(|stmt| stmt.fun_calls())
                )
                .collect(),
            Stmt::While(c, t) => c
                .fun_calls()
                .into_iter()
                .chain(t
                    .iter()
                    .flat_map(|stmt| stmt.fun_calls())
                )
                .collect(),
            Stmt::Assignment(_, _, e) => e.fun_calls(),
            Stmt::FunCall(fun_call) => {
                let mut fun_calls: BTreeSet<Id> = fun_call.args
                    .iter()
                    .flat_map(|arg| arg.fun_calls())
                    .collect();
                fun_calls.insert(fun_call.id.clone());
                fun_calls
            }
            Stmt::Return(e) => e
                .as_ref()
                .map_or(BTreeSet::new(), |e| e.fun_calls())
        }
    }

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        match self {
            Stmt::If(c, t, e) => c
                .references(exclude)
                .into_iter()
                .chain(t
                    .iter()
                    .flat_map(|stmt| stmt.references(exclude))
                )
                .chain(e
                    .iter()
                    .flat_map(|stmt| stmt.references(exclude))
                )
                .collect(),
            Stmt::While(c, t) => c
                .references(exclude)
                .into_iter()
                .chain(t
                    .iter()
                    .flat_map(|stmt| stmt.references(exclude))
                )
                .collect(),
            Stmt::Assignment(_, _, e) => e.references(exclude),
            Stmt::FunCall(fun_call) => fun_call.args
                .iter()
                .flat_map(|arg| arg.references(exclude))
                .collect(),
            Stmt::Return(e) => e
                .as_ref()
                .map_or(BTreeSet::new(), |e| e.references(exclude))
        }
    }

    fn assignments(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        match self {
            Stmt::If(_, t, e) => t
                .iter()
                .flat_map(|stmt| stmt.assignments(exclude))
                .chain(e
                    .iter()
                    .flat_map(|stmt| stmt.assignments(exclude))
                )
                .collect(),
            Stmt::While(_, t) => t
                .iter()
                .flat_map(|stmt| stmt.assignments(exclude))
                .collect(),
            Stmt::Assignment(id, _, _) => if exclude.contains(id) {
                BTreeSet::new()
            } else {
                Some(id.clone())
                    .into_iter()
                    .collect()
            },
            Stmt::FunCall(_) | Stmt::Return(_) => BTreeSet::new()
        }
    }
}

impl Calls for Exp {
    fn fun_calls(&self) -> BTreeSet<Id> {
        match self {
            Exp::Variable(_) | Exp::Number(_) | Exp::Character(_) | Exp::False | Exp::True | Exp::Nil => BTreeSet::new(),
            Exp::FunCall(fun_call) => {
                let mut fun_calls: BTreeSet<Id> = fun_call.args
                    .iter()
                    .flat_map(|arg| arg.fun_calls())
                    .collect();
                fun_calls.insert(fun_call.id.clone());
                fun_calls
            }
            Exp::Tuple(l, r) => l
                .fun_calls()
                .into_iter()
                .chain(r.fun_calls())
                .collect()
        }
    }

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        match self {
            Exp::Variable(id) => if exclude.contains(id) {
                BTreeSet::new()
            } else {
                Some(id.clone())
                    .into_iter()
                    .collect()
            }
            Exp::Number(_) | Exp::Character(_) | Exp::False | Exp::True | Exp::Nil => BTreeSet::new(),
            Exp::FunCall(fun_call) => fun_call.args
                .iter()
                .flat_map(|arg| arg.references(exclude))
                .collect(),
            Exp::Tuple(l, r) => l
                .references(exclude)
                .into_iter()
                .chain(r.references(exclude))
                .collect()
        }
    }

    fn assignments(&self, _: &HashSet<Id>) -> BTreeSet<Id> {
        // Expressions cannot assign values to other variables
        BTreeSet::new()
    }
}
