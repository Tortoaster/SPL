use error::Result;

use crate::binder::error::BindError::UnresolvedReference;
use crate::scope::Scope;
use crate::tree::{Decl, SPL};

pub trait Bindable<'a> {
    fn bind(&'a mut self, scope: Scope<'a>) -> Result<()>;
}

impl<'a> Bindable<'a> for SPL<'a> {
    fn bind(&'a mut self, mut scope: Scope<'a>) -> Result<()> {
        scope.open();
        self.0.iter().flat_map(|decl| if let Decl::FunDecl(d) = decl { Some(d) } else { None }).for_each(|d| scope.put_fun(d.0.0.clone(), d));
        self.0.iter().flat_map(|decl| if let Decl::VarDecl(d) = decl { Some(d) } else { None }).for_each(|d| scope.put_var(d.1.0.clone(), d));
        scope.close();
        Err(UnresolvedReference("Todo".to_owned()))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    pub type Result<T, E = BindError> = std::result::Result<T, E>;

    pub enum BindError {
        UnresolvedReference(String)
    }

    impl fmt::Display for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                BindError::UnresolvedReference(r) => write!(f, "Unresolved reference: {}", r)
            }
        }
    }

    impl Debug for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for BindError {}
}
