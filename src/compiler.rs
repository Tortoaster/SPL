use std::{env, fs};

use error::CompileError;
use error::Result;

use crate::lexer::Lexable;
use crate::tree::SPL;
use crate::typer::{Environment, Generator, InferMut};

pub fn compile() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(CompileError::InsufficientArguments);
    }

    let code = fs::read_to_string(&args[1]).expect("File inaccessible");

    let lexer = code.as_str().tokenize()?;
    let ast = SPL::new(lexer.peekable())?;

    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    ast.infer_type_mut(&mut env, &mut gen)?;

    println!("{}", ast);
    env
        .iter()
        .filter(|(id, _)|
            !vec![
                "print", "isEmpty", "fst", "snd", "hd", "tl",
                "not", "add", "sub", "mul", "div", "mod",
                "eq", "ne", "lt", "gt", "le", "ge",
                "and", "or", "cons"
            ].contains(&id.0.as_str())
        )
        .for_each(|(id, t)| println!("{}: {}", id.0, t));

    Ok(())
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::lexer::error::LexError;
    use crate::parser::error::ParseError;
    use crate::typer::error::TypeError;

    pub type Result<T, E = CompileError> = std::result::Result<T, E>;

    pub enum CompileError {
        LexError(Vec<LexError>),
        ParseError(ParseError),
        TypeError(TypeError),
        InsufficientArguments,
    }

    impl fmt::Display for CompileError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                CompileError::LexError(e) => write!(f, "Lexer error:\n{}", e.iter().map(|e| format!("{}", e)).collect::<Vec<String>>().join("\n")),
                CompileError::ParseError(e) => write!(f, "Parse error:\n{}", e),
                CompileError::TypeError(e) => write!(f, "Type error:\n{}", e),
                CompileError::InsufficientArguments => write!(f, "Not enough arguments")
            }
        }
    }

    impl Debug for CompileError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl From<Vec<LexError>> for CompileError {
        fn from(e: Vec<LexError>) -> Self {
            CompileError::LexError(e)
        }
    }

    impl From<ParseError> for CompileError {
        fn from(e: ParseError) -> Self {
            CompileError::ParseError(e)
        }
    }

    impl From<TypeError> for CompileError {
        fn from(e: TypeError) -> Self {
            CompileError::TypeError(e)
        }
    }

    impl Error for CompileError {}
}
