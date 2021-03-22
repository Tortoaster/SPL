use std::collections::HashMap;

use crate::binder::error::BindError;
use crate::binder::error::Result;
use crate::tree::{FunDecl, VarDecl, Id};

pub struct Scope<'a> {
    variables: Vec<HashMap<Id, &'a VarDecl<'a>>>,
    functions: Vec<HashMap<Id, &'a FunDecl<'a>>>,
}

impl<'a> Scope<'a> {
    pub fn new() -> Self {
        Scope {
            variables: Vec::new(),
            functions: Vec::new(),
        }
    }

    pub fn open(&mut self) {
        self.variables.push(HashMap::new());
        self.functions.push(HashMap::new());
    }

    pub fn close(&mut self) {
        self.variables.pop();
        self.functions.pop();
    }

    pub fn put_var(&mut self, query: Id, decl: &'a VarDecl<'a>) {
        self.variables.last_mut().expect("No scope found").insert(query, decl);
    }

    pub fn put_fun(&mut self, query: Id, decl: &'a FunDecl<'a>) {
        self.functions.last_mut().expect("No scope found").insert(query, decl);
    }

    pub fn get_var(&self, query: &Id) -> Option<&'a VarDecl<'a>> {
        self.variables.iter()
            .rev()
            .find_map(|m| m.get(query).map(|d| *d))
    }

    pub fn get_fun(&self, query: &Id) -> Option<&'a FunDecl<'a>> {
        self.functions.iter()
            .rev()
            .find_map(|m| m.get(query).map(|d| *d))
    }
}
