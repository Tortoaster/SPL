use std::{env, fs};

use error::Result;

use crate::error::CompileError;
use crate::lexer::Lexable;
use crate::tree::SPL;

mod char_iterator;
mod lexer;
mod parser;
mod typer;
mod tree;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(CompileError::InsufficientArguments);
    }

    let code = fs::read_to_string(&args[1]).expect("File inaccessible");

    let lexer = code.as_str().tokenize()?;
    let ast = SPL::new(lexer.peekable())?;
    // let _ = ast.bind()?;

    println!("{}", ast);

    Ok(())
}

mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::lexer::error::LexError;
    use crate::parser::error::ParseError;

    pub type Result<T, E = CompileError> = std::result::Result<T, E>;

    pub enum CompileError {
        LexError(Vec<LexError>),
        ParseError(ParseError),
        InsufficientArguments,
    }

    impl fmt::Display for CompileError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                CompileError::LexError(e) => write!(f, "Lexer error:\n{}", e.iter().map(|e| format!("{}", e)).collect::<Vec<String>>().join("\n")),
                CompileError::ParseError(e) => write!(f, "Parse error:\n{}", e),
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

    impl Error for CompileError {}
}
