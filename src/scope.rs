use std::collections::HashMap;

use crate::binder::error::BindError;
use crate::binder::error::Result;
use crate::parser::{FunDecl, VarDecl};

pub struct Scope<'a> {
    variables: Vec<HashMap<String, &'a VarDecl<'a>>>,
    functions: Vec<HashMap<String, &'a FunDecl<'a>>>,
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

    pub fn put_var(&mut self, query: String, decl: &'a VarDecl<'a>) {
        self.variables.last_mut().expect("No scope found").insert(query, decl);
    }

    pub fn put_fun(&mut self, query: String, decl: &'a FunDecl<'a>) {
        self.functions.last_mut().expect("No scope found").insert(query, decl);
    }

    pub fn get_var(&self, query: String) -> Result<&'a VarDecl<'a>> {
        self.variables.iter()
            .rev()
            .find_map(|m| m.get(&query).map(|d| *d))
            .ok_or(BindError::UnresolvedReference(query))
    }

    pub fn get_fun(&self, query: String) -> Result<&'a FunDecl<'a>> {
        self.functions.iter()
            .rev()
            .find_map(|m| m.get(&query).map(|d| *d))
            .ok_or(BindError::UnresolvedReference(query))
    }
}
