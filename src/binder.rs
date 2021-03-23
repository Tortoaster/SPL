use error::Result;

use crate::binder::error::BindError::UnresolvedReference;
use crate::tree::SPL;

pub trait Bindable {
    fn bind(&mut self) -> Result<()>;
}

impl Bindable for SPL {
    fn bind(&mut self) -> Result<()> {
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
