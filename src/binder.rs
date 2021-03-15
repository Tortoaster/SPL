use error::Result;

use crate::scope::Scope;
use crate::tree::{Decl, SPL, Exp};
use crate::binder::error::BindError;

pub trait Bindable<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()>;
}

impl<'a> Bindable<'a> for SPL<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        scope.open();
        self.0.iter().flat_map(|decl| if let Decl::FunDecl(d) = decl { Some(d) } else { None }).for_each(|d| scope.put_fun(d.0.clone(), d));
        self.0.iter().flat_map(|decl| if let Decl::VarDecl(d) = decl { Some(d) } else { None }).for_each(|d| scope.put_var(d.1.clone(), d));
        let errors: Vec<BindError> = self.0.iter().flat_map(|decl| decl.bind(scope).err()).flatten().collect();
        scope.close();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl<'a> Bindable<'a> for Decl<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        unimplemented!()
    }
}

impl<'a> Bindable<'a> for Exp<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        if let Exp::Variable(id, _, reference) = self {
            let found = scope.get_var(id).unwrap();
            reference.borrow_mut().replace(found);
        }
        Ok(())
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;
    use crate::tree::Id;

    pub type Result<T, E = Vec<BindError>> = std::result::Result<T, E>;

    pub enum BindError {
        UnresolvedReference(Id)
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
