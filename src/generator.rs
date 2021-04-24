use std::collections::HashSet;
use std::fmt;

use error::Result;

use crate::algorithm_w::{Space, Type};
use crate::generator::error::GenError;
use crate::ssm::prelude::*;
// Reserve first scratch register to keep track of global variables
use crate::ssm::Register::R0 as GP;
use crate::tree::{Decl, FunDecl, Id, SPL, VarDecl};
use crate::typer::DecoratedSPL;

const MAIN: &str = "main";

impl DecoratedSPL {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate()?.0 })
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
    fn generate(&self) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)>;
}

impl Gen for SPL {
    fn generate(&self) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        // Reserve space for global variables
        let globals = self.decls
            .iter()
            .filter(|decl| decl.space() == Space::Var)
            .count();
        let mut instructions = vec![
            Link { length: globals },
            LoadRegisterFromRegister { from: SP, to: GP }
        ];

        // Generate code to initialize global variables
        let (mut variables, var_variants) = self.decls
            .iter()
            .enumerate()
            .map(|(index, decl)| match decl {
                Decl::VarDecl(var_decl) => (var_decl, index).generate(),
                _ => Ok((Vec::new(), HashSet::new()))
            })
            .collect::<Result<Vec<(Vec<Instruction>, HashSet<(Id, Type)>)>>>()?
            .into_iter()
            .fold((Vec::new(), HashSet::new()), |(inst, variants), (new_inst, new_variants)|
                (inst.into_iter().chain(new_inst).collect(),
                 variants.into_iter().chain(new_variants).collect()),
            );
        instructions.append(&mut variables);

        // Move to main function
        instructions.push(Branch { label: Label::new(MAIN) });

        // Generate code for main function
        let (mut functions, fun_variants) = self.decls
            .iter()
            .find_map(|decl| match decl {
                Decl::FunDecl(fun_decl) => (fun_decl.id == Id(MAIN.to_owned())).then(|| fun_decl),
                _ => None
            })
            .ok_or(GenError::MissingMain)?
            .generate()?;
        instructions.append(&mut functions);

        let variants: HashSet<(Id, Type)> = var_variants.into_iter().chain(fun_variants).collect();

        // Keep generating necessary variants until all are done
        while !variants.is_empty() {

        }

        Ok((instructions, variants))
    }
}

/// Generate global variable
impl Gen for (&VarDecl, usize) {
    fn generate(&self) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        todo!()
    }
}

impl Gen for FunDecl {
    fn generate(&self) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
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
