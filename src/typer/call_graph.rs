use std::collections::{BTreeSet, HashMap, HashSet};

use petgraph::Graph;
use petgraph::prelude::*;

use crate::parser::{Decl, Exp, FunDecl, Id, PDecl, SPL, Stmt, VarDecl};
use crate::typer::Space;

type Node = usize;

struct Identifier {
    assigned: HashMap<(Id, Space), usize>,
    current: usize,
}

impl Identifier {
    fn new() -> Self {
        Identifier {
            assigned: HashMap::new(),
            current: 0,
        }
    }

    fn get(&mut self, index: &(Id, Space)) -> usize {
        let found = self.assigned.get(index);
        match found {
            None => {
                self.current += 1;
                self.assigned.insert(index.clone(), self.current);
                self.current
            }
            Some(n) => *n
        }
    }
}

pub fn topsorted_sccs<'a, 'b>(ast: &'b SPL<'a>) -> Vec<Vec<&'b PDecl<'a>>> {
    let mut ids = Identifier::new();

    let nodes: Vec<Node> = ast.decls
        .iter()
        .map(|decl| ids.get(&(decl.id(), decl.space())))
        .collect();

    let fun_calls: HashMap<Node, BTreeSet<Node>> = ast.decls
        .iter()
        .map(|decl| (ids.get(&(decl.id(), decl.space())), decl
            .fun_calls()
            .into_iter()
            .map(|id| ids.get(&(id, Space::Fun)))
            .collect())
        )
        .collect();

    let references: HashMap<Node, BTreeSet<Node>> = ast.decls
        .iter()
        .map(|decl| (ids.get(&(decl.id(), decl.space())), decl
            .references(&HashSet::new())
            .into_iter()
            .map(|id| ids.get(&(id, Space::Var)))
            .collect())
        )
        .collect();

    let assignments: HashMap<Node, BTreeSet<Node>> = ast.decls
        .iter()
        .map(|decl| (ids.get(&(decl.id(), decl.space())), decl
            .assignments(&HashSet::new())
            .into_iter()
            .map(|id| ids.get(&(id, Space::Var)))
            .collect())
        )
        .collect();

    let mut graph = Graph::<Node, ()>::new();

    let indices: HashMap<Node, NodeIndex> = nodes
        .iter()
        .map(|n| (*n, graph.add_node(*n)))
        .collect();

    fun_calls
        .into_iter()
        .chain(references)
        .chain(assignments)
        .for_each(|(n, es)| graph
            .extend_with_edges(es
                .into_iter()
                .flat_map(|e| indices.get(&e).copied())
                .zip(std::iter::repeat(indices[&n]))
            )
        );

    let inv_indices: HashMap<NodeIndex, Node> = indices
        .into_iter()
        .map(|(k, v)| (v, k))
        .collect();

    let inv_ids: HashMap<Node, (Id, Space)> = ids.assigned
        .into_iter()
        .map(|(k, v)| (v, k))
        .collect();

    let sccs = petgraph::algo::tarjan_scc(&graph)
        .into_iter()
        .map(|scc| scc
            .into_iter()
            .map(|index| {
                let node = inv_indices.get(&index).unwrap();
                inv_ids.get(&node).unwrap().clone()
            })
            .collect()
        )
        .collect::<Vec<Vec<(Id, Space)>>>();

    let decls: HashMap<(Id, Space), &PDecl> = ast.decls
        .iter()
        .map(|decl| ((decl.id(), decl.space()), decl))
        .collect();

    sccs
        .into_iter()
        .map(|scc| scc
            .into_iter()
            .map(|node| *decls.get(&node).unwrap())
            .collect()
        )
        .rev()
        .collect::<Vec<Vec<&PDecl>>>()
}

trait Calls {
    fn fun_calls(&self) -> BTreeSet<Id>;

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id>;

    fn assignments(&self, exclude: &HashSet<Id>) -> BTreeSet<Id>;
}

impl Calls for Decl<'_> {
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
            Decl::VarDecl(_) => BTreeSet::new(),
            Decl::FunDecl(decl) => decl.assignments(exclude)
        }
    }
}

impl Calls for FunDecl<'_> {
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
                defined.insert(decl.id.content.clone());
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
            .map(|decl| decl.id.content.clone())
            .collect();
        self.stmts
            .iter()
            .flat_map(|stmt| stmt.assignments(&defined))
            .collect()
    }
}

impl Calls for VarDecl<'_> {
    fn fun_calls(&self) -> BTreeSet<Id> {
        self.exp.fun_calls()
    }

    fn references(&self, exclude: &HashSet<Id>) -> BTreeSet<Id> {
        self.exp.references(exclude)
    }

    fn assignments(&self, _: &HashSet<Id>) -> BTreeSet<Id> {
        panic!("VarDecls cannot assign values to other variables")
    }
}

impl Calls for Stmt<'_> {
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
                fun_calls.insert(fun_call.id.content.clone());
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
                Some(id.content.clone())
                    .into_iter()
                    .collect()
            },
            Stmt::FunCall(_) | Stmt::Return(_) => BTreeSet::new()
        }
    }
}

impl Calls for Exp<'_> {
    fn fun_calls(&self) -> BTreeSet<Id> {
        match self {
            Exp::Variable(_) |
            Exp::Number(_) |
            Exp::Character(_) |
            Exp::Boolean(_) |
            Exp::Nil => BTreeSet::new(),
            Exp::FunCall(fun_call) => {
                let mut fun_calls: BTreeSet<Id> = fun_call.args
                    .iter()
                    .flat_map(|arg| arg.fun_calls())
                    .collect();
                fun_calls.insert(fun_call.id.content.clone());
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
            Exp::Number(_) | Exp::Character(_) | Exp::Boolean(_) | Exp::Nil => BTreeSet::new(),
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
        panic!("Expressions cannot assign values to other variables")
    }
}
