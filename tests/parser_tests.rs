use std::fs;

use spl::parser::SPL;
use spl::lexer::Lexable;

const RES_DIR: &str = "tests/res/";

#[test]
fn parse() {
    for dir in fs::read_dir(RES_DIR) {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect(format!("File {:?} is inaccessible", file.file_name()).as_str());
                let lexer = code.as_str().tokenize().expect("Failed to tokenize");
                SPL::new(lexer.peekable()).expect(format!("Error parsing {:?}", file.file_name()).as_str());
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
                if let Ok(ast) = SPL::new(lexer.peekable()) {
                    let pretty = format!("{}", ast);
                    let pretty_lexer = pretty.as_str().tokenize().expect("Failed to tokenize");
                    let pretty_ast = SPL::new(pretty_lexer.peekable()).expect(format!("Error parsing prettified {:?}", file.file_name()).as_str());
                    assert_eq!(ast, pretty_ast);
                }
            }
        }
    }
}
