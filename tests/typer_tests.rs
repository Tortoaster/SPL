use spl::lexer::Lexable;
use spl::parser::Parsable;
use spl::tree::Exp;
use spl::typer::{Environment, Generator, Infer, Type};
use spl::compiler::error::CompileError;
use spl::typer::error::TypeError;

// env
//         .iter()
//         .filter(|(id, _)| !vec!["print", "isEmpty", "fst", "snd", "hd", "tl", "not", "add", "sub", "mul", "div", "mod", "eq", "ne", "lt", "gt", "le", "ge", "and", "or", "cons"].contains(&id.0.as_str()))
//         .for_each(|(id, t)| println!("{}: {}", id.0, t));

#[test]
fn test_simple_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "1 + 1".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Int, inferred);

    Ok(())
}

#[test]
fn test_list_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "'a' : []".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Array(Box::new(Type::Char)), inferred);

    Ok(())
}

#[test]
fn test_invalid_list() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "1 : 'a' : []".tokenize()?.peekable())?;
    let result = exp.infer_type(&env, &mut gen).err().unwrap();

    assert_eq!(TypeError::Mismatch { expected: Type::Char, found: Type::Int }, result);

    Ok(())
}
