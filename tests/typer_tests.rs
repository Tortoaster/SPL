use std::fs;

use spl::compiler::error::CompileError;
use spl::lexer::Lexable;
use spl::parser::{Exp, Id, Parsable, SPL};
use spl::position::Pos;
use spl::typer::{Environment, Generator, Infer, Space, Type, TypeClass};
use spl::typer::error::TypeError;

#[test]
fn simple_exp() {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "1 + 1".tokenize().unwrap().peekable()).unwrap();
    let (_, inferred) = exp.infer(&env, &mut gen).unwrap();

    assert_eq!(Type::Int, inferred.content);
}

#[test]
fn list_exp() {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "'a' : []".tokenize().unwrap().peekable()).unwrap();
    let (_, inferred) = exp.infer(&env, &mut gen).unwrap();

    if let Type::Array(t) = inferred.content {
        assert_eq!(Type::Char, t.content);
    } else {
        panic!();
    }
}

#[test]
fn invalid_list() {
    let mut gen = Generator::new();
    let env = Environment::new();

    let exp = Exp::parse(&mut "1 : 'a' : []".tokenize().unwrap().peekable()).unwrap();
    let result = exp.infer(&env, &mut gen);

    assert_eq!(TypeError::Mismatch { expected: Type::Char, found: Type::Int }, result.err().unwrap().content);
}

#[test]
fn assignment() {
    let env = type_check("
    var x = [];
    f() {
        x = 1 : x;
    }
    ").unwrap();

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

    if let Type::Array(t) = &result.inner.content {
        assert_eq!(Type::Int, t.content);
    } else {
        panic!();
    }
}

#[test]
fn return_type() {
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
    ").unwrap();
}

#[test]
fn no_return() {
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

    if let CompileError::TypeError(Pos { content: TypeError::Incomplete(Id(f)), .. }) = result.err().unwrap() {
        assert_eq!("f", f);
    } else {
        panic!()
    }
}

#[test]
fn void_return() {
    type_check("
    f() {
        var x = 1;
        x = x + 1;
        if(x < 5) {
            return;
        }
        x = x + 2;
    }
    ").unwrap();
}

#[test]
fn bad_return() {
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

    if let CompileError::TypeError(Pos { content: TypeError::Mismatch { expected, found }, .. }) = result.err().unwrap() {
        assert_eq!(Type::Int, expected);
        assert_eq!(Type::Bool, found);
    } else {
        panic!()
    }
}

#[test]
fn fields() {
    let env = type_check("
    var x = [];
    f() {
        x.tl.hd.fst.snd = True;
    }
    ").unwrap();

    let result = env.get(&(Id("x".to_owned()), Space::Var)).unwrap();

    if let Type::Array(result) = &result.inner.content {
        if let Type::Tuple(result, _) = &result.content {
            if let Type::Tuple(_, result) = &result.content {
                assert_eq!(Type::Bool, result.content);
                return;
            }
        }
    }

    panic!("Does not match fields: {:?}", result);
}

#[test]
fn infer_mono_function() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "test(x) { x = x + 1; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();

    let result = env.get(&(Id("test".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Void", format!("{}", result));
}

#[test]
fn infer_poly_function() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "id(x) { return x; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();

    let result = env.get(&(Id("id".to_owned()), Space::Fun)).unwrap();

    assert_eq!("a -> a", format!("{}", result));
}

#[test]
fn conflict_function() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "test(x) :: Bool -> Void { x = x + 1; }".tokenize().unwrap().peekable()).unwrap();
    let result = program.infer_types(&mut env, &mut gen);

    assert_eq!(TypeError::Mismatch { expected: Type::Int, found: Type::Bool }, result.err().unwrap().content);
}

#[test]
fn mut_rec() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "a(x) { return b(x); } b(x) { return c(x + 1); } c(x) { return a(x) + 1; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();

    let result_a = env.get(&(Id("a".to_owned()), Space::Fun)).unwrap();
    let result_b = env.get(&(Id("b".to_owned()), Space::Fun)).unwrap();
    let result_c = env.get(&(Id("c".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Int", format!("{}", result_a));
    assert_eq!("Int -> Int", format!("{}", result_b));
    assert_eq!("Int -> Int", format!("{}", result_c));
}

#[test]
fn generalized_in_time() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "id1(x) { return x; } main(x) { id1(x); return id2(x + 1) + 1; } id2(x) { return x; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();

    let result_main = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();
    let result_id1 = env.get(&(Id("id1".to_owned()), Space::Fun)).unwrap();
    let result_id2 = env.get(&(Id("id2".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Int -> Int", format!("{}", result_main));
    assert_eq!("a -> a", format!("{}", result_id1));
    assert_eq!("a -> a", format!("{}", result_id2));
}

#[test]
fn allowed_overloading() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < 10; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();
}

#[test]
fn strict_overloading() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "main(x, y) { return x > 'a' && y < True; }".tokenize().unwrap().peekable()).unwrap();
    let result = program.infer_types(&mut env, &mut gen);

    assert_eq!(TypeError::TypeClass { found: Type::Bool, class: TypeClass::Ord }, result.err().unwrap().content);
}

#[test]
fn flow_overloading() {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut "main(x) { return x == x; }".tokenize().unwrap().peekable()).unwrap();
    program.infer_types(&mut env, &mut gen).unwrap();

    let result = env.get(&(Id("main".to_owned()), Space::Fun)).unwrap();

    assert_eq!("Eq a => a -> Bool", format!("{}", result));
}

#[test]
fn type_check_files() {
    let mut errors = 0;

    for dir in fs::read_dir("tests/res/") {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect("File inaccessible");

                let lexer = code.as_str().tokenize().unwrap();
                let mut ast = SPL::new(lexer.peekable()).unwrap();

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
    }
}

fn type_check(code: &str) -> Result<Environment, CompileError> {
    let mut gen = Generator::new();
    let mut env = Environment::new();

    let mut program = SPL::parse(&mut code.tokenize()?.peekable())?;
    program.infer_types(&mut env, &mut gen)?;

    Ok(env)
}
