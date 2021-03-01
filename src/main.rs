use std::{env, fmt};
use std::error::Error;
use std::fs;

use spl::lexer::{Lexable, LexError};

use crate::parser::ParseError;
use crate::parser::SPL;
use std::fmt::Debug;

mod char_iterator;
mod lexer;
mod parser;

type Result<T, E = CompileError> = std::result::Result<T, E>;

enum CompileError {
    LexError(Vec<LexError>),
    ParseError(ParseError),
    InsufficientArguments
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

impl From<ParseError> for CompileError {
    fn from(e: ParseError) -> Self {
        CompileError::ParseError(e)
    }
}

impl Error for CompileError {}

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(CompileError::InsufficientArguments);
    }

    let code = fs::read_to_string(&args[1]).expect("File inaccessible");

    let mut lexer = code.as_str().tokenize();
    while let Some(_) = lexer.next() {}
    if !lexer.errors.is_empty() {
        return Err(CompileError::LexError(lexer.errors));
    }

    let ast = SPL::new(code.as_str())?;

    println!("{}", ast);

    Ok(())
}
