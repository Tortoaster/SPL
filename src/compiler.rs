use error::Result;

use crate::generator::Program;
use crate::lexer::Lexable;
use crate::parser::SPL;
use crate::typer::{Environment, Generator};

pub fn compile(code: &str) -> Result<Program> {
    let lexer = code.tokenize()?;
    let mut ast = SPL::new(lexer.peekable())?;

    let mut gen = Generator::new();
    let mut env = Environment::new();

    ast.infer_types(&mut env, &mut gen)?;

    // println!("{}", env
    //     .iter()
    //     .map(|((id, _), t)| format!("{}: {}", id, t))
    //     .collect::<Vec<String>>()
    //     .join("\n")
    // );

    let program = ast.generate_code()?;

    Ok(program)
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::generator::error::GenError;
    use crate::lexer::error::LexError;
    use crate::parser::error::ParseError;
    use crate::position::Pos;
    use crate::typer::error::TypeError;

    pub type Result<'a, T, E = CompileError<'a>> = std::result::Result<T, E>;

    pub enum CompileError<'a> {
        LexError(Vec<Pos<'a, LexError>>),
        ParseError(Pos<'a, ParseError>),
        TypeError(Pos<'a, TypeError>),
        GenError(GenError),
        InsufficientArguments,
    }

    impl fmt::Display for CompileError<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                CompileError::LexError(e) => write!(f, "Lexer error:\n{}", e.iter().map(|e| format!("{}", e)).collect::<Vec<String>>().join("\n")),
                CompileError::ParseError(e) => write!(f, "Parse error:\n{}", e),
                CompileError::TypeError(e) => write!(f, "Type error:\n{}", e),
                CompileError::GenError(e) => write!(f, "Generator error:\n{}", e),
                CompileError::InsufficientArguments => write!(f, "Not enough arguments")
            }
        }
    }

    impl Debug for CompileError<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl<'a> From<Vec<Pos<'a, LexError>>> for CompileError<'a> {
        fn from(e: Vec<Pos<'a, LexError>>) -> Self {
            CompileError::LexError(e)
        }
    }

    impl<'a> From<Pos<'a, ParseError>> for CompileError<'a> {
        fn from(e: Pos<'a, ParseError>) -> Self {
            CompileError::ParseError(e)
        }
    }

    impl<'a> From<Pos<'a, TypeError>> for CompileError<'a> {
        fn from(e: Pos<'a, TypeError>) -> Self {
            CompileError::TypeError(e)
        }
    }

    impl From<GenError> for CompileError<'_> {
        fn from(e: GenError) -> Self {
            CompileError::GenError(e)
        }
    }

    impl Error for CompileError<'_> {}
}
