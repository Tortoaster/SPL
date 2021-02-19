use std::fs;

use spl::parser::SPL;

const RES_DIR: &str = "tests/res/";

#[test]
fn parse() {
    for dir in fs::read_dir(RES_DIR) {
        for file in dir {
            if let Ok(file) = file {
                let code = fs::read_to_string(file.path()).expect(format!("File {:?} is inaccessible", file.file_name()).as_str());
                SPL::new(code.as_str()).expect(format!("Error parsing {:?}", file.file_name()).as_str());
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
                if let Ok(ast) = SPL::new(code.as_str()) {
                    let pretty = format!("{}", ast);
                    let pretty_ast = SPL::new(pretty.as_str()).expect(format!("Error parsing prettified {:?}", file.file_name()).as_str());
                    assert_eq!(ast, pretty_ast);
                }
            }
        }
    }
}
