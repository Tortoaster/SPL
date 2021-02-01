use std::fmt;

use crate::lexer::{Lexer, InfixOp, Token, PrefixOp, Expr};
use std::iter::Peekable;

type ParseError = String;

impl PrefixOp {
    fn binding_strength(&self) -> ((), u8) {
        match self {
            PrefixOp::Not => ((), 7),
        }
    }
}

impl InfixOp {
    fn binding_strength(&self) -> (u8, u8) {
        match self {
            InfixOp::Times | InfixOp::Divide | InfixOp::Modulo => (15, 16),
            InfixOp::Plus | InfixOp::Minus => (13, 14),
            InfixOp::Smaller | InfixOp::Greater | InfixOp::SmallerEqual | InfixOp::GreaterEqual => (11, 12),
            InfixOp::Equals | InfixOp::NotEqual => (9, 10),
            InfixOp::And => (5, 6),
            InfixOp::Or => (3, 4),
            InfixOp::Cons => (2, 1),
        }
    }
}

pub enum AST {
    AtomId(String),
    AtomNum(i32),
    AtomChar(char),
    Atom(Expr),
    Cons(InfixOp, Vec<AST>),
    PrefixedCons(PrefixOp, Vec<AST>),
}

pub fn parse(input: &str) -> Result<AST, ParseError> {
    let mut lexer = Lexer::new(input).peekable();
    parse_expr(&mut lexer, 0)
}

fn parse_expr(lexer: &mut Peekable<Lexer>, min_bp: u8) -> Result<AST, ParseError> {
    let mut lhs = match lexer.next() {
        Some(Token::Id(id)) => AST::AtomId(id),
        Some(Token::Expression(e)) => AST::Atom(e),
        Some(Token::Number(n)) => AST::AtomNum(n),
        Some(Token::Character(c)) => AST::AtomChar(c),
        Some(Token::Op1(op)) => {
            let ((), r_bp) = op.binding_strength();
            let rhs = parse_expr(lexer, r_bp)?;
            AST::PrefixedCons(op.clone(), vec![rhs])
        }
        t => Err(format!("bad token: {:?}", t))?,
    };

    loop {
        let op = match lexer.peek() {
            None => break,
            Some(Token::Op2(op)) => op.clone(),
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
            AST::AtomId(id) => write!(f, "{}", id),
            AST::AtomNum(n) => write!(f, "{}", n),
            AST::AtomChar(c) => write!(f, "{}", c),
            AST::Atom(e) => write!(f, "{:?}", e),
            AST::Cons(head, rest) => {
                write!(f, "({:?}", head)?;
                for s in rest {
                    write!(f, " {}", s)?
                }
                write!(f, ")")
            }
            AST::PrefixedCons(head, rest) => {
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
