use spl::compiler::error::CompileError;
use spl::lexer::Lexable;
use spl::parser::Parsable;
use spl::tree::{Exp, Stmt, VarDecl, Id, SPL};
use spl::typer::{Environment, Generator, Infer, Type, InferMut, TryInfer};
use spl::typer::error::TypeError;
use spl::typer::Typed;
use std::fs;
use spl::compiler;

#[test]
fn simple_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "1 + 1".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Int, inferred);

    Ok(())
}

#[test]
fn list_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "'a' : []".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Array(Box::new(Type::Char)), inferred);

    Ok(())
}

#[test]
fn invalid_list() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "1 : 'a' : []".tokenize()?.peekable())?;
    let result = exp.infer_type(&env, &mut gen).err().unwrap();

    assert_eq!(TypeError::Mismatch { expected: Type::Char, found: Type::Int }, result);

    Ok(())
}

#[test]
fn assignment() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let decl = VarDecl::parse(&mut "var x = [];".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let assignment = Stmt::parse(&mut "x = 1 : x;".tokenize()?.peekable())?;
    let (subst, _) = assignment.try_infer_type(&mut env, &mut gen)?;
    env = env.apply(&subst);

    let result = env.get(&Id("x".to_owned())).unwrap();

    assert_eq!(&env.generalize(&Type::Array(Box::new(Type::Int))), result);

    Ok(())
}

#[test]
fn return_type() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let decl = VarDecl::parse(&mut "var x = 1;".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let stmts = Stmt::parse_many(&mut "x = x + 1; if(x < 5) { return True; } else { return False; } x = x + 2;".tokenize()?.peekable());
    let (_, ret_type) = stmts.try_infer_type(&mut env, &mut gen)?;

    assert_eq!(Some(Type::Bool), ret_type);

    Ok(())
}

#[test]
fn no_return() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let decl = VarDecl::parse(&mut "var x = 1;".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let stmts = Stmt::parse_many(&mut "x = x + 1; if(x < 5) { return True; } else {  } x = x + 2;".tokenize()?.peekable());
    let (_, ret_type) = stmts.try_infer_type(&mut env, &mut gen)?;

    assert_eq!(None, ret_type);

    Ok(())
}

#[test]
fn bad_return() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let decl = VarDecl::parse(&mut "var x = 1;".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let stmts = Stmt::parse_many(&mut "x = x + 1; if(x < 5) { return True; } else { return 1; } x = x + 2;".tokenize()?.peekable());
    let result = stmts.try_infer_type(&mut env, &mut gen);

    assert_eq!(Err(TypeError::Mismatch { expected: Type::Int, found: Type::Bool }), result);

    Ok(())
}

#[test]
fn fields() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let decl = VarDecl::parse(&mut "var x = [];".tokenize()?.peekable())?;
    decl.infer_type_mut(&mut env, &mut gen)?;
    let stmt = Stmt::parse(&mut "x.tl.hd.fst.snd = True;".tokenize()?.peekable())?;
    let (subst, _) = stmt.try_infer_type(&mut env, &mut gen)?;
    env = env.apply(&subst);

    let result = env.get(&Id("x".to_owned())).unwrap();

    if let Type::Array(result) = &result.inner {
        if let Type::Tuple(result, _) = &**result {
            if let Type::Tuple(_, result) = &**result {
                assert_eq!(Type::Bool, **result);
                return Ok(());
            }
        }
    }
    panic!("Does not match fields: {:?}", result);
}

#[test]
fn infer_mono_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "test(x) { x = x + 1; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&Id("test".to_owned())).unwrap();

    assert_eq!("(Int -> Void)", format!("{}", result));

    Ok(())
}

#[test]
fn infer_poly_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "id(x) { return x; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&Id("id".to_owned())).unwrap();

    assert_eq!("(a -> a)", format!("{}", result));

    Ok(())
}

#[test]
fn check_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "test(x) :: a -> Void { x = x + 1; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&Id("test".to_owned())).unwrap();

    assert_eq!("(Int -> Void)", format!("{}", result));

    Ok(())
}

#[test]
fn conflict_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "test(x) :: Bool -> Void { x = x + 1; }".tokenize()?.peekable())?;
    let result = program.infer_type_mut(&mut env, &mut gen);

    assert_eq!(Err(TypeError::Mismatch { expected: Type::Bool, found: Type::Int }), result);

    Ok(())
}

#[test]
fn type_check_files() -> Result<(), CompileError> {
    let mut errors = 0;

    for dir in fs::read_dir("tests/res/") {
        for file in dir {
            if let Ok(file) = file {
                let result = compiler::compile(file.path());
                match result {
                    Ok(_) => if file.file_name().into_string().unwrap().ends_with("shouldfail.spl") {
                        eprintln!("{:?}: Should fail but does not", file.file_name());
                        errors += 1;
                    }
                    Err(e) => if !file.file_name().into_string().unwrap().ends_with("shouldfail.spl") {
                        eprintln!("{:?}: {}", file.file_name(), e);
                        errors += 1;
                    }
                }
            }
        }
    }

    if errors > 0 {
        panic!("Errors found while typing")
    } else {
        Ok(())
    }
}
