use crate::compiler::error::CompileError;
use std::env;

mod char_iterator;
mod lexer;
mod parser;
mod typer;
mod tree;
mod compiler;

fn main() -> Result<(), CompileError> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(CompileError::InsufficientArguments);
    }

    let (ast, env) = compiler::compile(&args[1])?;

    println!("{}", ast);
    env
        .iter()
        .filter(|(id, _)|
            !vec![
                "print", "isEmpty", "fst", "snd", "hd", "tl",
                "!", "+", "-", "*", "/", "%",
                "==", "!=", "<", ">", "<=", ">=",
                "&&", "||", ":"
            ].contains(&id.0.as_str())
        )
        .for_each(|(id, t)| println!("{}: {}", id.0, t));

    Ok(())
}
