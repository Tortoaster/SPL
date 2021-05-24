use std::process::Command;
use spl::compiler;
use std::fs;

#[test]
fn file_try() {
    let code = fs::read_to_string("tests/res/try.spl").expect("File inaccessible");

    let program = compiler::compile(code.as_str()).unwrap();

    fs::write("tests/out/try.ssm", format!("{}", program)).expect("Unable to write file");

    let output = Command::new("java -jar ssm/ssm.jar --file tests/out/try.ssm --cli --haltonerror")
        .output()
        .expect("Error running SSM");

    let out = String::from_utf8(output.stdout).unwrap();

    println!("{}", out);

    let numbers = out
        .lines()
        .next()
        .unwrap_or(String::from_utf8(output.stderr).unwrap().as_str())
        .to_owned();

    assert_eq!(numbers, "012345678");
}
