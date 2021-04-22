use std::env;

use crate::compiler::error::CompileError;

mod char_iterator;
mod lexer;
mod parser;
mod typer;
mod tree;
mod compiler;
mod call_graph;
mod algorithm_w;
mod generator;
mod ssm;

fn main() -> Result<(), CompileError> {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        return Err(CompileError::InsufficientArguments);
    }

    let env = compiler::compile(&args[1])?;

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
