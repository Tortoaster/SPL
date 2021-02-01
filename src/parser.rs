use std::fmt;

use crate::lexer::{Lexer, Token, Operator};
use std::iter::Peekable;

type ParseError = String;

impl Operator {
    fn prefix_binding_power(&self) -> Result<((), u8), ParseError> {
        let bp = match self {
            Operator::Not => ((), 7),
            o => Err(format!("{:?} is not a prefix operator", o))?
        };

        Ok(bp)
    }
    
    fn infix_binding_power(&self) -> Result<(u8, u8), ParseError> {
        let bp = match self {
            Operator::Times | Operator::Divide | Operator::Modulo => (15, 16),
            Operator::Plus | Operator::Minus => (13, 14),
            Operator::Smaller | Operator::Greater | Operator::SmallerEqual | Operator::GreaterEqual => (11, 12),
            Operator::Equals | Operator::NotEqual => (9, 10),
            Operator::And => (5, 6),
            Operator::Or => (3, 4),
            Operator::Cons => (2, 1),
            o => Err(format!("{:?} is not an infix operator", o))?
        };

        Ok(bp)
    }
}

pub enum AST {
    Identifier(String),
    Number(i32),
    Character(char),
    Cons(Operator, Vec<AST>),
}

pub fn parse(input: &str) -> Result<AST, ParseError> {
    let mut lexer = Lexer::new(input).peekable();
    parse_expr(&mut lexer, 0)
}

fn parse_expr(lexer: &mut Peekable<Lexer>, min_bp: u8) -> Result<AST, ParseError> {
    let mut lhs = match lexer.next() {
        Some(Token::Identifier(id)) => AST::Identifier(id),
        Some(Token::Number(n)) => AST::Number(n),
        Some(Token::Character(c)) => AST::Character(c),
        Some(Token::Operator(op)) => {
            let ((), r_bp) = op.prefix_binding_power()?;
            let rhs = parse_expr(lexer, r_bp)?;
            AST::Cons(op.clone(), vec![rhs])
        }
        t => Err(format!("bad token: {:?}", t))?,
    };

    loop {
        let op = match lexer.peek() {
            None => break,
            Some(Token::Operator(op)) => op.clone(),
            t => Err(format!("bad token: {:?}", t))?,
        };

        let (l_bp, r_bp) = op.infix_binding_power()?;

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
            AST::Identifier(id) => write!(f, "{}", id),
            AST::Number(n) => write!(f, "{}", n),
            AST::Character(c) => write!(f, "{}", c),
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
