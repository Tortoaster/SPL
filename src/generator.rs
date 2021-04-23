use std::fmt;

use error::Result;

use crate::ssm::{Instruction, Label};
use crate::ssm::prelude::*;
use crate::tree::{Decl, SPL};
use crate::typer::DecoratedSPL;

impl DecoratedSPL {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate()? })
    }
}

pub struct Program {
    instructions: Vec<Instruction>
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in &self.instructions {
            writeln!(f, "{}", i)?;
        }
        Ok(())
    }
}

trait Gen {
    fn generate(&self) -> Result<Vec<Instruction>>;
}

impl Gen for SPL {
    fn generate(&self) -> Result<Vec<Instruction>> {
        Ok(vec![
            Branch { label: Label::new("m") },

            Labeled(Label::new("f"), Box::new(Link { length: 1 })),
            LoadConstant(4),
            StoreLocal { offset: 1 },
            LoadLocal { offset: -3 },
            LoadLocal { offset: -2 },
            Add,
            LoadLocal { offset: 1 },
            Add,
            StoreRegister { reg: RR },
            Unlink,
            Return,

            Labeled(Label::new("m"), Box::new(LoadConstant(30))),
            LoadConstant(8),
            BranchSubroutine { label: Label::new("f") },
            AdjustStack { offset: -2 },
            LoadRegister { reg: RR },
            Trap { trap: PrintInt },
            Halt,
        ])
        // Ok(self.decls
        //     .iter()
        //     .map(|decl| decl.generate())
        //     .collect::<Result<Vec<Vec<Instruction>>>>()?
        //     .into_iter()
        //     .flatten()
        //     .collect())
    }
}

impl Gen for Decl {
    fn generate(&self) -> Result<Vec<Instruction>> {
        todo!()
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

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
