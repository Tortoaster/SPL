use std::fs;

use spl::algorithm_w::{Environment, Generator, Space, Type, TypeClass};
use spl::compiler::error::CompileError;
use spl::lexer::Lexable;
use spl::parser::Parsable;
use spl::tree::{Exp, Id, SPL};
use spl::typer::error::TypeError;
use spl::typer::Infer;

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

    assert_eq!(TypeError::Mismatch { expected: Type::Int, found: Type::Char }, result);

    Ok(())
}

#[test]
fn assignment() -> Result<(), CompileError> {
    let env = type_check("
    var x = [];
    f() {
        x = 1 : x;
    }
    ")?;

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

    assert_eq!(Type::Array(Box::new(Type::Int)).generalize(&env), *result);

    Ok(())
}

#[test]
fn return_type() -> Result<(), CompileError> {
    type_check("
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

    Ok(())
}

#[test]
fn no_return() -> Result<(), CompileError> {
    let result = type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return True;
        }
        x = x + 2;
    }
    ");

    if let CompileError::TypeError(TypeError::Incomplete(Id(f))) = result.err().unwrap() {
        assert_eq!("f", f);
    } else {
        panic!()
    }

    Ok(())
}

#[test]
fn void_return() -> Result<(), CompileError> {
    type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return;
        }
        x = x + 2;
    }
    ")?;

    Ok(())
}

#[test]
fn bad_return() -> Result<(), CompileError> {
    let result = type_check("
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
    ");

    if let CompileError::TypeError(TypeError::Mismatch { expected, found }) = result.err().unwrap() {
        assert_eq!(Type::Bool, expected);
        assert_eq!(Type::Int, found);
    } else {
        panic!()
    }

    Ok(())
}

#[test]
fn fields() -> Result<(), CompileError> {
    let env = type_check("
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
    let mut env = Environment::new();

    let program = SPL::parse(&mut "test(x) { x = x + 1; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    let result = env.get(&(Id("test".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Void", format!("{}", result));

    Ok(())
}

#[test]
fn infer_poly_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "id(x) { return x; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    let result = env.get(&(Id("id".to_owned()), Space::Fun)).unwrap();

    assert_eq!("a -> a", format!("{}", result));

    Ok(())
}

#[test]
fn conflict_function() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "test(x) :: Bool -> Void { x = x + 1; }".tokenize()?.peekable())?;
    let result = program.infer_types(&mut env, &mut gen);

    assert_eq!(TypeError::Mismatch { expected: Type::Int, found: Type::Bool }, result.err().unwrap());

    Ok(())
}

#[test]
fn mut_rec() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "a(x) { return b(x); } b(x) { return c(x + 1); } c(x) { return a(x) + 1; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    let result_a = env.get(&(Id("a".to_owned()), Space::Fun)).unwrap();
    let result_b = env.get(&(Id("b".to_owned()), Space::Fun)).unwrap();
    let result_c = env.get(&(Id("c".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Int", format!("{}", result_a));
    assert_eq!("Int -> Int", format!("{}", result_b));
    assert_eq!("Int -> Int", format!("{}", result_c));

    Ok(())
}

#[test]
fn generalized_in_time() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "id1(x) { return x; } main(x) { id1(x); return id2(x + 1) + 1; } id2(x) { return x; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    let result_main = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();
    let result_id1 = env.get(&(Id("id1".to_owned()), Space::Fun)).unwrap();
    let result_id2 = env.get(&(Id("id2".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Int", format!("{}", result_main));
    assert_eq!("a -> a", format!("{}", result_id1));
    assert_eq!("a -> a", format!("{}", result_id2));

    Ok(())
}

#[test]
fn allowed_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < 10; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    Ok(())
}

#[test]
fn strict_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < True; }".tokenize()?.peekable())?;
    let result = program.infer_types(&mut env, &mut gen);

    assert_eq!(TypeError::TypeClass { found: Type::Bool, class: TypeClass::Ord }, result.err().unwrap());

    Ok(())
}

#[test]
fn flow_overloading() -> Result<(), CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut "main(x) { return x == x; }".tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    let result = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Eq a => a -> Bool", format!("{}", result));

    Ok(())
}

fn type_check(code: &str) -> Result<Environment, CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let program = SPL::parse(&mut code.tokenize()?.peekable())?;

    program.infer_types(&mut env, &mut gen)?;

    Ok(env)
}

#[test]
fn type_check_files() -> Result<(), CompileError> {
    let mut errors = 0;

    for dir in fs::read_dir("tests/res/") {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect("File inaccessible");

                let lexer = code.as_str().tokenize()?;
                let ast = SPL::new(lexer.peekable())?;

                let mut gen = Generator::new();
                let mut env = Environment::new();

                let result = ast.infer_types(&mut env, &mut gen);

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
