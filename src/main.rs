use std::env;
use std::fs;
use crate::parser::SPL;
use crate::parser::Result;

mod char_iterator;
mod lexer;
mod parser;

fn main() -> Result<()> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(String::from("Not enough arguments"));
    }

    let code = fs::read_to_string(&args[1]).expect("File inaccessible");

    let ast = SPL::new(code.as_str())?;

    println!("{}", ast);

    Ok(())
}
