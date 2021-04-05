use spl::compiler::error::CompileError;
use spl::lexer::Lexable;
use spl::parser::Parsable;
use spl::tree::{Exp, Stmt, VarDecl, Id};
use spl::typer::{Environment, Generator, Infer, Type, InferMut};
use spl::typer::error::TypeError;
use spl::typer::Typed;

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

#[test]
fn test_assignment() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let decl = VarDecl::parse(&mut "var x = [];".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let assignment = Stmt::parse(&mut "x = 1 : x;".tokenize()?.peekable())?;
    let (subst, _) = assignment.infer_type(&mut env, &mut gen, &Type::Void)?;
    env = env.apply(&subst);

    let (id, result) = env
        .iter()
        .find(|(id, _)| {
            !vec![
                "print", "isEmpty", "fst", "snd", "hd", "tl",
                "not", "add", "sub", "mul", "div", "mod",
                "eq", "ne", "lt", "gt", "le", "ge",
                "and", "or", "cons"
            ].contains(&id.0.as_str())
        })
        .unwrap();

    assert_eq!(&Id("x".to_owned()), id);
    assert_eq!(&env.generalize(&Type::Array(Box::new(Type::Int))), result);

    Ok(())
}
