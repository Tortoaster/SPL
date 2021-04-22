use crate::ssm::Instruction;
use crate::tree::{Decl, SPL};

use error::Result;
use crate::typer::DecoratedSPL;

trait Gen {
    fn generate(&self) -> Result<Vec<Instruction>>;
}

impl DecoratedSPL {
    pub fn generate_code(&self) -> Result<Vec<Instruction>> {
        self.generate()
    }
}

impl Gen for SPL {
    fn generate(&self) -> Result<Vec<Instruction>> {
        Ok(self.decls
            .iter()
            .map(|decl| decl.generate())
            .collect::<Result<Vec<Vec<Instruction>>>>()?
            .into_iter()
            .flatten()
            .collect())
    }
}

impl Gen for Decl {
    fn generate(&self) -> Result<Vec<Instruction>> {
        todo!()
    }
}

pub mod error {
    use std::fmt;
    use std::fmt::Debug;
    use std::error::Error;

    pub type Result<T, E = GenError> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum GenError {
        MissingMain
    }

    impl fmt::Display for GenError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                GenError::MissingMain => write!(f, "No main function found")
            }
        }
    }

    impl Debug for GenError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for GenError {}
}
