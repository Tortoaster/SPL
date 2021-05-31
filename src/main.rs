use std::{env, fs};
use std::path::Path;

use crate::compiler::error::CompileError;

mod lexer;
mod parser;
mod typer;
mod compiler;
mod generator;
mod position;

const DIR: &str = "./out/";
const EXTENSION: &str = ".ssm";

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("{}", CompileError::InsufficientArguments);
        return;
    }

    let path = Path::new(&args[1]);

    let code = fs::read_to_string(path).expect("File inaccessible");

    let result = compiler::compile(code.as_str());

    match result {
        Err(err) => {
            eprintln!("{}", err);
            return;
        }
        Ok(program) => {
            let out = (DIR.to_owned() + path
                .file_stem()
                .expect("Not a file")
                .to_str()
                .unwrap()
            ).to_owned() + EXTENSION;

            fs::write(&out, format!("{}", program))
                .expect("Unable to write file");
            println!("Output file written to {}", out);
        }
    }
}
