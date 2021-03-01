use std::{env, fmt};
use std::error::Error;
use std::fs;

use spl::lexer::{Lexable, LexError};

use crate::parser::ParseError;
use crate::parser::SPL;

mod char_iterator;
mod lexer;
mod parser;

type Result<'a, T, E = CompileError<'a>> = std::result::Result<T, E>;

#[derive(Debug)]
enum CompileError<'a> {
    LexError(Vec<LexError<'a>>),
    ParseError(ParseError),
    InsufficientArguments
}

impl fmt::Display for CompileError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CompileError::LexError(e) => write!(f, "Lexer error: {:#?}", e),
            CompileError::ParseError(e) => write!(f, "Parse error: {}", e),
            CompileError::InsufficientArguments => write!(f, "Not enough arguments")
        }
    }
}

impl From<ParseError> for CompileError<'_> {
    fn from(e: ParseError) -> Self {
        CompileError::ParseError(e)
    }
}

impl Error for CompileError<'_> {}

fn main() -> Result<'static, ()> {
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
