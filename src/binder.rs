use crate::parser::{FunDecl, Id, VarDecl};
use std::collections::HashMap;
use std::fmt;
use std::fmt::Debug;
use std::error::Error;

type Result<T, E = BindError> = std::result::Result<T, E>;

enum BindError {
    Todo
}

impl fmt::Display for BindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BindError::Todo => write!(f, "Todo")
        }
    }
}

impl Debug for BindError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Error for BindError {}

trait Bindable {
    fn find(&self, fun_decls: &mut HashMap<Id, &FunDecl>, var_decls: &mut HashMap<Id, &VarDecl>);

    fn bind(&self, fun_decls: &HashMap<Id, &FunDecl>, var_decls: &HashMap<Id, &VarDecl>) -> Result<()>;
}
