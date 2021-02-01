use std::env;
use std::fs;

mod lexer;
mod parser;

fn main() -> Result<(), String> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(String::from("Not enough arguments"));
    }

    let code = fs::read_to_string(&args[1]).expect("File inaccessible");

    let ast = parser::parse(&code[..])?;

    println!("{}", ast);

    Ok(())
}
