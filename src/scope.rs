use std::collections::HashMap;

use crate::binder::error::BindError;
use crate::tree::{FunDecl, VarDecl, Id};

pub type Result<T, E = BindError> = std::result::Result<T, E>;

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

    pub fn put_var(&mut self, id: Id, decl: &'a VarDecl<'a>) -> Result<()> {
        match self.variables.last_mut().expect("No scope found").insert(id.clone(), decl) {
            None => Ok(()),
            Some(_) => Err(BindError::Redefined(id))
        }
    }

    pub fn put_fun(&mut self, id: Id, decl: &'a FunDecl<'a>) -> Result<()> {
        match self.functions.last_mut().expect("No scope found").insert(id.clone(), decl) {
            None => Ok(()),
            Some(_) => Err(BindError::Redefined(id))
        }
    }

    pub fn get_var(&self, id: &Id) -> Result<&'a VarDecl<'a>> {
        self.variables.iter()
            .rev()
            .find_map(|m| m.get(id).map(|d| *d))
            .ok_or(BindError::UnresolvedReference(id.clone()))
    }

    pub fn get_fun(&self, id: &Id) -> Result<&'a FunDecl<'a>> {
        self.functions.iter()
            .rev()
            .find_map(|m| m.get(id).map(|d| *d))
            .ok_or(BindError::UnresolvedReference(id.clone()))
    }
}
