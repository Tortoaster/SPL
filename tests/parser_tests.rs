use std::fs;

use spl::parser::SPL;

const RES_DIR: &str = "tests/res/";

#[test]
fn tests() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "fac.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn two_d() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "2D.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn three_d() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "3D.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}
