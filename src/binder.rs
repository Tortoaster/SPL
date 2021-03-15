use error::Result;

use crate::parser::SPL;
use crate::binder::error::BindError;

pub trait Bindable {
    fn bind(&self) -> Result<()>;
}

impl Bindable for SPL {
    fn bind(&self) -> Result<()> {
        Err(BindError::Todo)
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    pub type Result<T, E = BindError> = std::result::Result<T, E>;

    pub enum BindError {
        Todo
    }

    impl fmt::Display for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "todo")
        }
    }

    impl Debug for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for BindError {}
}
