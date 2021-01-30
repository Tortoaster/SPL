use std::fmt;
use std::fmt::{Display, Formatter};

use crate::lexer::Lexer;

pub struct AST {

}

impl Display for AST {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "")
    }
}

impl <'a> Lexer<'a> {
    pub fn parse(self) -> Result<AST, String> {
        Err(String::from("Not implemented"))
    }
}
