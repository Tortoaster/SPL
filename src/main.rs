use std::{env, fs};

use error::Result;

use crate::error::CompileError;
use spl::lexer::Lexable;
use spl::tree::SPL;
use spl::typer::{Environment, Generator, Typed};
use spl::typer::InferMut;
use spl::tree::Exp;
use spl::parser::Parsable;
use spl::typer::Infer;
use spl::typer::PolyType;
use spl::tree::Id;
use spl::tree::Stmt;
use spl::typer::TryInfer;

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

    let mut environment = Environment::new();
    let mut generator = Generator::new();

    for (name, annotation) in vec![
        ("print", "a -> Void"),
        ("isEmpty", "[a] -> Bool"),
        ("hd", "[a] -> a"),
        ("tl", "[a] -> [a]"),
        ("fst", "(a, b) -> a"),
        ("snd", "(a, b) -> b"),
        ("not", "Bool -> Bool"),
        ("add", "Int Int -> Int"),
        ("sub", "Int Int -> Int"),
        ("mul", "Int Int -> Int"),
        ("div", "Int Int -> Int"),
        ("mod", "Int Int -> Int"),
        ("eq", "a a -> Bool"),
        ("ne", "a a -> Bool"),
        ("lt", "Int Int -> Bool"),
        ("gt", "Int Int -> Bool"),
        ("le", "Int Int -> Bool"),
        ("ge", "Int Int -> Bool"),
        ("and", "Bool Bool -> Bool"),
        ("or", "Bool Bool -> Bool"),
        ("cons", "a [a] -> [a]"),
    ] {
        let mut t: PolyType = annotation.parse().unwrap();
        t = environment.generalize(&t.instantiate(&mut generator));
        environment.insert(Id(name.to_owned()), t);
    }

    let exp = Exp::parse(&mut "('a' : []) : []".tokenize()?.peekable())?;
    let (subst, inferred) = exp.infer_type(&environment, &mut generator)?;
    environment = environment.apply(&subst);
    println!("{}", environment.generalize(&inferred));

    // ast.infer_type_mut(&mut environment, &mut generator)?;
    //
    // println!("{}", ast);
    environment
        .iter()
        .filter(|(id, _)| !vec!["print", "isEmpty", "fst", "snd", "hd", "tl", "not", "add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "gt", "le", "ge", "and", "or", "cons"].contains(&id.0.as_str()))
        .for_each(|(id, t)| println!("{}: {}", id.0, t));

    Ok(())
}

mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use spl::lexer::error::LexError;
    use spl::parser::error::ParseError;
    use spl::typer::error::TypeError;

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
