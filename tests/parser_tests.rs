use std::fs;

use spl::lexer::Lexable;
use spl::parser::SPL;

const RES_DIR: &str = "tests/res/";

#[test]
fn parse() {
    for dir in fs::read_dir(RES_DIR) {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect(format!("File {:?} is inaccessible", file.file_name()).as_str());
                let lexer = code.as_str().tokenize().expect("Failed to tokenize");
                let _ = SPL::new(lexer.peekable()).expect(format!("Error parsing {:?}", file.file_name()).as_str());
            }
        }
    }
}

#[test]
fn pretty_print() {
    for dir in fs::read_dir(RES_DIR) {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect(format!("File {:?} is inaccessible", file.file_name()).as_str());
                let lexer = code.as_str().tokenize().expect("Failed to tokenize");
                let result = SPL::new(lexer.peekable());
                if let Ok(ast) = result {
                    let pretty_code = format!("{}", ast.content);
                    let pretty_lexer = pretty_code.as_str().tokenize().expect("Failed to tokenize");
                    let pretty_ast = SPL::new(pretty_lexer.peekable()).expect(format!("Error parsing prettified {:?}", file.file_name()).as_str());
                    assert_eq!(format!("{}", ast.content), format!("{}", pretty_ast.content));
                }
            }
        }
    }
}
