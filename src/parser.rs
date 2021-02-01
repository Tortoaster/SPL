use std::fmt;

use crate::lexer::{Lexer, Op, Token};
use std::iter::Peekable;

type ParseError = String;

impl Op {
    fn binding_strength(&self) -> (u8, u8) {
        match self {
            Op::Times | Op::Divide | Op::Modulo => (13, 14),
            Op::Plus | Op::Minus => (11, 12),
            Op::Cons => (10, 9),
            Op::Smaller | Op::Greater | Op::SmallerEqual | Op::GreaterEqual => (7, 8),
            Op::Equals | Op::NotEqual => (5, 6),
            Op::And => (3, 4),
            Op::Or => (1, 2),
        }
    }
}

pub enum AST {
    Atom(String),
    Cons(Op, Vec<AST>),
}

pub fn parse(input: &str) -> Result<AST, ParseError> {
    let mut lexer = Lexer::new(input).peekable();
    parse_expr(&mut lexer, 0)
}

fn parse_expr(lexer: &mut Peekable<Lexer>, min_bp: u8) -> Result<AST, ParseError> {
    let mut lhs = match lexer.next() {
        Some(Token::Id(id)) => AST::Atom(id),
        t => Err(format!("bad token: {:?}", t))?,
    };

    loop {
        let op = match lexer.peek() {
            None => break,
            Some(Token::Operation(op)) => op.clone(),
            t => Err(format!("bad token: {:?}", t))?,
        };

        let (l_bp, r_bp) = op.binding_strength();

        if l_bp < min_bp {
            break;
        }

        lexer.next();
        let rhs = parse_expr(lexer, r_bp)?;

        lhs = AST::Cons(op, vec![lhs, rhs]);
    }

    Ok(lhs)
}

impl fmt::Display for AST {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AST::Atom(i) => write!(f, "{}", i),
            AST::Cons(head, rest) => {
                write!(f, "({:?}", head)?;
                for s in rest {
                    write!(f, " {}", s)?
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::parser::{parse, ParseError};

    #[test]
    fn infix() -> Result<(), ParseError> {
        let s = parse("a + b * c * d + e")?;

        assert_eq!(s.to_string(), "(Plus (Plus a (Times (Times b c) d)) e)");

        Ok(())
    }
}
