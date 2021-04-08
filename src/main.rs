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
        .filter(|((id, _), _)|
            !vec![
                "print", "isEmpty", "fst", "snd", "hd", "tl", "not", "add", "sub", "mul", "div",
                "mod", "eq", "ne", "lt", "gt", "le", "ge", "and", "or", "cons"
            ].contains(&id.0.as_str())
        )
        .for_each(|((id, _), t)| println!("{}: {}", id.0, t));

    Ok(())
}
