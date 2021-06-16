use std::fs;
use std::path::Path;
use std::process::Command;

use spl::compiler;

const TEST_DIR: &str = "tests/res/";

fn get_output<P: AsRef<Path>>(path: P) -> Option<String> {
    const TEMP: &str = "tests/out/";
    let name = path
        .as_ref()
        .file_stem()
        .expect("Not a file")
        .to_str()
        .unwrap();
    let file = TEMP.to_owned() + name + ".ssm";

    let code = fs::read_to_string(path).expect("File inaccessible");
    let program = compiler::compile(code.as_str()).ok()?;

    fs::write(&file, format!("{}", program))
        .expect("Unable to write file");

    let output = Command::new("java")
        .arg("-jar")
        .arg("ssm/ssm.jar")
        .arg("--file")
        .arg(file)
        .arg("--cli")
        .arg("--haltonerror")
        .output()
        .expect("Error running SSM");

    Some(String::from_utf8(output.stdout).unwrap())
}

#[test]
fn run_try() {
    let numbers = get_output(TEST_DIR.to_owned() + "try.spl")
        .expect("Failed to get output")
        .lines()
        .next()
        .unwrap()
        .to_owned();

    assert_eq!(numbers, "0123456789(1, 0)");
}

#[test]
fn run_lists() {
    let numbers = get_output(TEST_DIR.to_owned() + "lists.spl")
        .expect("Failed to get output")
        .lines()
        .next()
        .unwrap()
        .to_owned();

    assert_eq!(numbers, "915");
}

#[test]
fn run_sum() {
    let numbers = get_output(TEST_DIR.to_owned() + "sum.spl")
        .expect("Failed to get output")
        .lines()
        .next()
        .unwrap()
        .to_owned();

    assert_eq!(numbers, "666");
}
