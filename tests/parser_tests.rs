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

#[test]
fn a_bit_of_everything() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "a_bit_of_everything.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn arguments() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "arguments.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn bool() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "bool.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn brainfuck() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "brainfuck.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn comment() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "comment.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn constants() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "constants.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn empty() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "empty.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn example() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "example.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn fac() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "fac.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn identity() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "identity.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn infinite_type_shouldfail() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "infinite_type_shouldfail.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn integers() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "integers.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn list() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "list.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn lists() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "lists.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn many_parenthesis() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "many_parenthesis.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn more_parenthesis() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "more_parenthesis.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn mutrec() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "mutrec.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn op() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "op.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn overloading() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "overloading.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn polymorphic_value_again_shouldfail() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "polymorphic_value_again_shouldfail.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn polymorphic_value_indirect_shouldfail() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "polymorphic_value_indirect_shouldfail.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn polymorphic_value_shouldfail() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "polymorphic_value_shouldfail.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn problematic() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "problematic.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn problematic_programs() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "problematic_programs.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn recursion() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "recursion.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn return_ill_typed() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "return_ill_typed.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn return_in_all_code_paths() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "return_in_all_code_paths.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn return_well_typed() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "return_well_typed.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn self_application_shouldfail() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "self_application_shouldfail.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn shadow() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "shadow.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn sieve() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "sieve.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn stress_test() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "stress_test.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn sum() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "sum.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn sum_product() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "SumProduct.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn unary_minus() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "unary_minus.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn while_() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "while.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn whitespaces() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "whitespaces.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}

#[test]
fn x() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "x.spl").expect("File inaccessible");
    SPL::new(code.as_str()).unwrap();
}
