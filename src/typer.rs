use std::fmt;
use std::error::Error;
use std::fmt::Debug;

type Result<T, E = TypeError> = std::result::Result<T, E>;

enum TypeError {
    TypeMismatch
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::TypeMismatch => write!(f, "Type mismatch")
        }
    }
}

impl Debug for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Error for TypeError {}
