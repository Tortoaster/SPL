use crate::compiler::error::CompileError;

mod char_iterator;
mod lexer;
mod parser;
mod typer;
mod tree;
mod compiler;

fn main() -> Result<(), CompileError> {
    compiler::compile()
}
