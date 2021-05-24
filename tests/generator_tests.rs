use std::process::Command;
use spl::compiler;
use std::fs;

#[test]
fn file_try() {
    let code = fs::read_to_string("tests/res/try.spl").expect("File inaccessible");

    let program = compiler::compile(code.as_str()).unwrap();

    fs::write("tests/out/try.ssm", format!("{}", program)).expect("Unable to write file");

    let output = Command::new("java")
        .arg("-jar")
        .arg("ssm/ssm.jar")
        .arg("--file")
        .arg("tests/out/try.ssm")
        .arg("--cli")
        .arg("--haltonerror")
        .output()
        .expect("Error running SSM");

    let numbers = String::from_utf8(output.stdout)
        .unwrap()
        .lines()
        .next()
        .unwrap()
        .to_owned();

    assert_eq!(numbers, "012345678");
}
