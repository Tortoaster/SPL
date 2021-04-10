use spl::compiler::error::CompileError;
use spl::lexer::Lexable;
use spl::parser::Parsable;
use spl::tree::{Exp, Id, SPL};
use spl::typer::{Environment, Generator, Infer, Type, InferMut, Space};
use spl::typer::error::TypeError;
use std::fs;
use spl::compiler;

#[test]
fn simple_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "1 + 1".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Int, inferred);

    Ok(())
}

#[test]
fn list_exp() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "'a' : []".tokenize()?.peekable())?;
    let (_, inferred) = exp.infer_type(&env, &mut gen)?;

    assert_eq!(Type::Array(Box::new(Type::Char)), inferred);

    Ok(())
}

#[test]
fn invalid_list() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let env = Environment::new(&mut gen);

    let exp = Exp::parse(&mut "1 : 'a' : []".tokenize()?.peekable())?;
    let result = exp.infer_type(&env, &mut gen).err().unwrap();

    assert_eq!(TypeError::Mismatch { expected: Type::Char, found: Type::Int }, result);

    Ok(())
}

#[test]
fn assignment() -> Result<(), CompileError> {
    let (_, env) = type_check("
    var x = [];
    f() {
        x = 1 : x;
    }
    ")?;

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

    assert_eq!(&env.generalize(&Type::Array(Box::new(Type::Int))), result);

    Ok(())
}

#[test]
fn return_type() -> Result<(), CompileError> {
    let (result, _) = type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return True;
        } else {
            return False;
        }
        x = x + 2;
    }
    ")?;

    assert_eq!(Ok(Type::Void), result);

    Ok(())
}

#[test]
fn no_return() -> Result<(), CompileError> {
    let (result, _) = type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return True;
        } else {}
        x = x + 2;
    }
    ")?;

    assert_eq!(Err(TypeError::Incomplete(Id("f".to_owned()))), result);

    Ok(())
}

#[test]
fn bad_return() -> Result<(), CompileError> {
    let (result, _) = type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return True;
        } else {
            return 1;
        }
        x = x + 2;
    }
    ")?;

    assert_eq!(Err(TypeError::Mismatch { expected: Type::Bool, found: Type::Int }), result);

    Ok(())
}

#[test]
fn fields() -> Result<(), CompileError> {
    let (_, env) = type_check("
    var x = [];
    f() {
        x.tl.hd.fst.snd = True;
    }
    ")?;

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

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
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "test(x) { x = x + 1; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&(Id("test".to_owned()), Space::Fun)).unwrap();

    assert_eq!("(Int -> Void)", format!("{}", result));

    Ok(())
}

#[test]
fn infer_poly_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "id(x) { return x; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&(Id("id".to_owned()), Space::Fun)).unwrap();

    assert_eq!("(a -> a)", format!("{}", result));

    Ok(())
}

#[test]
fn check_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "test(x) :: a -> Void { x = x + 1; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&(Id("test".to_owned()), Space::Fun)).unwrap();

    assert_eq!("(Int -> Void)", format!("{}", result));

    Ok(())
}

#[test]
fn conflict_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "test(x) :: Bool -> Void { x = x + 1; }".tokenize()?.peekable())?;
    let result = program.infer_type_mut(&mut env, &mut gen);

    assert_eq!(Err(TypeError::Mismatch { expected: Type::Bool, found: Type::Int }), result);

    Ok(())
}

#[test]
fn mut_rec() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "a(x) { return b(x); } b(x) { return c(x + 1); } c(x) { return a(x) + 1; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result_a = env.get(&(Id("a".to_owned()), Space::Fun)).unwrap();
    let result_b = env.get(&(Id("b".to_owned()), Space::Fun)).unwrap();
    let result_c = env.get(&(Id("c".to_owned()), Space::Fun)).unwrap();

    assert_eq!("(Int -> Int)", format!("{}", result_a));
    assert_eq!("(Int -> Int)", format!("{}", result_b));
    assert_eq!("(Int -> Int)", format!("{}", result_c));

    Ok(())
}

#[test]
fn generalized_in_time() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "id1(x) { return x; } main(x) { id1(x); return id2(x + 1) + 1; } id2(x) { return x; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result_main = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();
    let result_id1 = env.get(&(Id("id1".to_owned()), Space::Fun)).unwrap();
    let result_id2 = env.get(&(Id("id2".to_owned()), Space::Fun)).unwrap();

    assert_eq!("(Int -> Int)", format!("{}", result_main));
    assert_eq!("(a -> a)", format!("{}", result_id1));
    assert_eq!("(a -> a)", format!("{}", result_id2));

    Ok(())
}

#[test]
fn allowed_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < 10; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    Ok(())
}

#[test]
fn strict_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < True; }".tokenize()?.peekable())?;
    let result = program.infer_type_mut(&mut env, &mut gen);

    assert_eq!(Err(TypeError::TypeClass { found: Type::Bool, class: Id("Ord".to_owned()) }), result);

    Ok(())
}

#[test]
fn flow_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "main(x) { return x == x; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Eq a => (a -> Bool)", format!("{}", result));

    Ok(())
}

// TODO: Decide what to do when this happens
#[ignore]
#[test]
fn no_alias() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut "var x = []; var y = x; main() { y = 1 : y; }".tokenize()?.peekable())?;
    program.infer_type_mut(&mut env, &mut gen)?;

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

    assert_eq!("[a]", format!("{}", result));

    Ok(())
}

fn type_check(code: &str) -> Result<(Result<Type, TypeError>, Environment), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new(&mut gen);

    let program = SPL::parse(&mut code.tokenize()?.peekable())?;

    Ok((program.infer_type_mut(&mut env, &mut gen), env))
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
