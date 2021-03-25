use std::iter::Peekable;

use error::Result;

use crate::lexer::{Lexer, Operator, Token};
use crate::tree::{BasicType, Decl, Exp, FunCall, FunDecl, FunType, Id, RetType, Selector, SPL, Stmt, Type, VarDecl, VarType};
use crate::parser::error::ParseError;
use crate::char_iterator::Positioned;

trait Parsable: Sized {
    /**
    Parses this parsable. This consumes the necessary tokens from the iterator,
    hence this should only be used when no alternative parsables are valid.
    **/
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self>;

    /**
    Tries to parse this parsable. If it succeeds, this returns the same value as parse,
    but if it fails, this function won't advance the iterator (at the cost of performance).
    **/
    fn try_parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut copy = (*tokens).clone();
        let parsed = Self::parse(&mut copy)?;
        *tokens = copy;
        Ok(parsed)
    }

    /**
    Parses as many instances of this parsable after each other as possible.
    **/
    fn parse_many(tokens: &mut Peekable<Lexer>) -> Vec<Self> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
        }
        parsed
    }

    /**
    Parses as many instances of this parsable after each other as possible, separated by separator.
    **/
    fn parse_many_sep(tokens: &mut Peekable<Lexer>, separator: &Token) -> Result<Vec<Self>> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
            match tokens.peek() {
                None => break,
                Some(s) => if *separator != **s { break }
            }
            munch(tokens, separator)?;
        }
        Ok(parsed)
    }
}

fn munch(tokens: &mut Peekable<Lexer>, expected: &Token) -> Result<()> {
    let found = tokens.next().ok_or(ParseError::EOF { expected: format!("{:?}", expected) })?;

    if *found == *expected {
        Ok(())
    } else {
        Err(ParseError::BadToken {
            found: (*found).clone(),
            row: found.row,
            col: found.col,
            code: found.code.to_owned(),
            expected: format!("{:?}", expected)
        })
    }
}

impl SPL {
    pub fn new(mut lexer: Peekable<Lexer>) -> Result<Self> {
        Self::parse(&mut lexer)
    }
}

impl Parsable for SPL {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut decls = Vec::new();

        while tokens.peek().is_some() {
            let d = Decl::parse(tokens)?;
            decls.push(d);
        }

        Ok(SPL { decls })
    }
}

impl Parsable for Decl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let decl = match **tokens.peek().ok_or(ParseError::EOF { expected: "declaration".to_owned() })? {
            Token::Identifier(_) => Decl::FunDecl(FunDecl::parse(tokens)?),
            _ => Decl::VarDecl(VarDecl::parse(tokens)?)
        };

        Ok(decl)
    }
}

impl Parsable for VarDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = VarType::parse(tokens)?;
        let id = Id::parse(tokens)?;
        munch(tokens, &Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        munch(tokens, &Token::Semicolon)?;

        Ok(VarDecl { var_type, id, exp })
    }
}

impl Parsable for FunDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let id = Id::parse(tokens)?;
        munch(tokens, &Token::OpenParen)?;
        let args = Id::parse_many_sep(tokens, &Token::Comma)?;
        munch(tokens, &Token::CloseParen)?;

        let fun_type = if let Some(Positioned { inner: Token::HasType, .. } ) = tokens.peek() {
            munch(tokens, &Token::HasType)?;
            Some(FunType::parse(tokens)?)
        } else {
            None
        };

        munch(tokens, &Token::OpenBracket)?;
        let var_decls = VarDecl::parse_many(tokens);
        let stmts = Stmt::parse_many(tokens);
        munch(tokens, &Token::CloseBracket)?;

        Ok(FunDecl { id, args, fun_type, var_decls, stmts })
    }
}

impl Parsable for VarType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = match **tokens.peek().ok_or(ParseError::EOF { expected: "variable type".to_owned() })? {
            Token::Var => {
                munch(tokens, &Token::Var)?;
                VarType::Var
            }
            _ => VarType::Type(Type::parse(tokens)?)
        };

        Ok(var_type)
    }
}

impl Parsable for RetType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let ret_type = match **tokens.peek().ok_or(ParseError::EOF { expected: "return type".to_owned() })? {
            Token::Void => {
                munch(tokens, &Token::Void)?;
                RetType::Void
            }
            _ => RetType::Type(Type::parse(tokens)?)
        };

        Ok(ret_type)
    }
}

impl Parsable for FunType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let arg_types = Type::parse_many(tokens);
        munch(tokens, &Token::To)?;
        let ret_type = RetType::parse(tokens)?;
        Ok(FunType { arg_types, ret_type })
    }
}

impl Parsable for Type {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let t = match **tokens.peek().ok_or(ParseError::EOF { expected: "type".to_owned() })? {
            Token::OpenParen => {
                munch(tokens, &Token::OpenParen)?;
                let l = Type::parse(tokens)?;
                munch(tokens, &Token::Comma)?;
                let r = Type::parse(tokens)?;
                munch(tokens, &Token::CloseParen)?;
                Type::Tuple(Box::new(l), Box::new(r))
            }
            Token::OpenArr => {
                munch(tokens, &Token::OpenArr)?;
                let t = Type::parse(tokens)?;
                munch(tokens, &Token::CloseArr)?;
                Type::Array(Box::new(t))
            }
            Token::Identifier(_) => Type::Generic(Id::parse(tokens)?),
            _ => Type::BasicType(BasicType::parse(tokens)?)
        };

        Ok(t)
    }
}

impl Parsable for BasicType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let t = match tokens.next().ok_or(ParseError::EOF { expected: "Int, Bool, or Char".to_owned() })? {
            Positioned { inner: Token::Int, .. } => BasicType::Int,
            Positioned { inner: Token::Bool, .. } => BasicType::Bool,
            Positioned { inner: Token::Char, .. } => BasicType::Char,
            token => return Err(ParseError::BadToken {
                found: (*token).clone(),
                row: token.row,
                col: token.col,
                code: token.code.to_owned(),
                expected: "Int, Bool, or Char".to_owned()
            })
        };

        Ok(t)
    }
}

impl Parsable for Stmt {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        let t = match tokens.next().ok_or(ParseError::EOF { expected: "statement".to_owned() })? {
            Positioned { inner: Token::If, .. } => {
                munch(tokens, &Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                munch(tokens, &Token::CloseParen)?;
                munch(tokens, &Token::OpenBracket)?;
                let then = Stmt::parse_many(tokens);
                munch(tokens, &Token::CloseBracket)?;
                let otherwise = if let Some(Positioned { inner: Token::Else, .. }) = tokens.peek() {
                    munch(tokens, &Token::Else)?;
                    munch(tokens, &Token::OpenBracket)?;
                    let result = Stmt::parse_many(tokens);
                    munch(tokens, &Token::CloseBracket)?;
                    result
                } else {
                    Vec::new()
                };

                Stmt::If(condition, then, otherwise)
            }
            Positioned { inner: Token::While, .. } => {
                munch(tokens, &Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                munch(tokens, &Token::CloseParen)?;
                munch(tokens, &Token::OpenBracket)?;
                let repeat = Stmt::parse_many(tokens);
                munch(tokens, &Token::CloseBracket)?;

                Stmt::While(condition, repeat)
            }
            Positioned { inner: Token::Return, .. } => {
                let value = if let Some(Positioned { inner: Token::Semicolon, .. }) = tokens.peek() {
                    None
                } else {
                    Some(Exp::parse(tokens)?)
                };
                munch(tokens, &Token::Semicolon)?;

                Stmt::Return(value)
            }
            Positioned { inner: Token::Identifier(s), .. } => {
                let id = Id(s);
                if let Some(Positioned { inner: Token::OpenParen, .. }) = tokens.peek() {
                    munch(tokens, &Token::OpenParen)?;
                    let args = Exp::parse_many_sep(tokens, &Token::Comma)?;
                    munch(tokens, &Token::CloseParen)?;
                    munch(tokens, &Token::Semicolon)?;

                    Stmt::FunCall(FunCall { id, args })
                } else {
                    let selector = Selector::parse(tokens)?;
                    munch(tokens, &Token::Assign)?;
                    let exp = Exp::parse(tokens)?;
                    munch(tokens, &Token::Semicolon)?;

                    Stmt::Assignment(id, selector, exp)
                }
            }
            token => return Err(ParseError::BadToken {
                found: (*token).clone(),
                row: token.row,
                col: token.col,
                code: token.code.to_owned(),
                expected: "statement".to_owned()
            })
        };

        Ok(t)
    }
}

impl Exp {
    fn parse_exp(tokens: &mut Peekable<Lexer>, min_bp: u8) -> Result<Self> {
        let mut lhs = match tokens.next().ok_or(ParseError::EOF { expected: "expression".to_owned() })? {
            Positioned { inner: Token::Identifier(s), .. } => {
                let id = Id(s);
                if let Some(Positioned { inner: Token::OpenParen, .. }) = tokens.peek(){
                    munch(tokens, &Token::OpenParen)?;
                    let fun_call = FunCall { id, args: Exp::parse_many_sep(tokens, &Token::Comma)? };
                    munch(tokens, &Token::CloseParen)?;
                    Exp::FunCall(fun_call)
                } else {
                    let selector = Selector::parse(tokens)?;
                    selector.fields.into_iter().fold(Exp::Variable(id), |e, f| Exp::FunCall(FunCall { id: Id(format!("{}", f)), args: vec![e] }))
                }
            }
            Positioned { inner: Token::Operator(op), row, col, .. } => {
                let r_bp = op.prefix_binding_power(row, col)?;
                let rhs = Self::parse_exp(tokens, r_bp)?;
                Exp::UnaryOp(op.clone(), Box::new(rhs))
            }
            Positioned { inner: Token::Number(n), .. } => Exp::Number(n),
            Positioned { inner: Token::Character(c), .. } => Exp::Character(c),
            Positioned { inner: Token::False, .. } => Exp::False,
            Positioned { inner: Token::True, .. } => Exp::True,
            Positioned { inner: Token::OpenParen, .. } => {
                let lhs = Self::parse_exp(tokens, 0)?;
                if let Some(Positioned { inner: Token::CloseParen, .. }) = tokens.peek() {
                    munch(tokens, &Token::CloseParen)?;
                    lhs
                } else {
                    munch(tokens, &Token::Comma)?;
                    let rhs = Self::parse_exp(tokens, 0)?;
                    munch(tokens, &Token::CloseParen)?;
                    Exp::Tuple(Box::new(lhs), Box::new(rhs))
                }
            }
            Positioned { inner: Token::Nil, .. } => Exp::Nil,
            token => return Err(ParseError::BadToken {
                found: (*token).clone(),
                row: token.row,
                col: token.col,
                code: token.code.to_owned(),
                expected: "expression".to_owned()
            })
        };

        while let Some(Positioned { inner: Token::Operator(op), row, col, .. }) = tokens.peek() {
            let (l_bp, r_bp) = op.infix_binding_power(*row, *col)?;

            if l_bp < min_bp {
                break;
            }

            let op = match *tokens.next().unwrap() {
                Token::Operator(ref op) => op.clone(),
                _ => panic!("Impossible"),
            };
            let rhs = Self::parse_exp(tokens, r_bp)?;

            lhs = Exp::BinaryOp(op, Box::new(lhs), Box::new(rhs));
        }

        Ok(lhs)
    }
}

impl Operator {
    fn prefix_binding_power(&self, row: usize, col: usize) -> Result<u8> {
        let bp = match self {
            Operator::Minus => 17,
            Operator::Not => 7,
            op => return Err(ParseError::Fixity {
                found: op.clone(),
                prefix: true,
                row,
                col,
                code: "TODO".to_string()
            })
        };

        Ok(bp)
    }

    fn infix_binding_power(&self, row: usize, col: usize) -> Result<(u8, u8)> {
        let bp = match self {
            Operator::Times | Operator::Divide | Operator::Modulo => (15, 16),
            Operator::Plus | Operator::Minus => (13, 14),
            Operator::Smaller | Operator::Greater |
            Operator::SmallerEqual | Operator::GreaterEqual => (11, 12),
            Operator::Equals | Operator::NotEqual => (9, 10),
            Operator::And => (6, 5),
            Operator::Or => (4, 3),
            Operator::Cons => (2, 1),
            op => return Err(ParseError::Fixity {
                found: op.clone(),
                prefix: false,
                row,
                col,
                code: "TODO".to_string()
            })
        };

        Ok(bp)
    }
}

impl Parsable for Exp {
    fn parse(lexer: &mut Peekable<Lexer>) -> Result<Self> {
        Self::parse_exp(lexer, 0)
    }
}

impl Parsable for Selector {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut fields = Vec::new();

        while let Some(Positioned { inner: Token::Field(_), .. }) = tokens.peek() {
            match tokens.next() {
                Some(Positioned { inner: Token::Field(field), .. }) => fields.push(field),
                _ => panic!("Impossible")
            }
        }

        Ok(Selector { fields })
    }
}

impl Parsable for Id {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match tokens.next().ok_or(ParseError::EOF { expected: "identifier".to_owned() })? {
            Positioned { inner: Token::Identifier(s), .. } => Ok(Id(s)),
            token => return Err(ParseError::BadToken {
                found: (*token).clone(),
                row: token.row,
                col: token.col,
                code: token.code.to_owned(),
                expected: "identifier".to_owned()
            })
        }
    }
}

pub mod error {
    use crate::lexer::{Token, Operator};
    use std::fmt;
    use std::fmt::Debug;
    use std::error::Error;

    pub type Result<T, E = ParseError> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum ParseError {
        BadToken {
            found: Token,
            row: usize,
            col: usize,
            code: String,
            expected: String,
        },
        EOF {
            expected: String
        },
        Fixity {
            found: Operator,
            prefix: bool,
            row: usize,
            col: usize,
            code: String
        },
    }

    impl fmt::Display for ParseError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                ParseError::BadToken { found, row, col, code: _, expected } => write!(
                    f,
                    "Bad token {:?} at {}:{}:\n{}\n{: >indent$}\nExpected: {}",
                    found,
                    row,
                    col,
                    "TODO",
                    // code.lines().nth(*row - 1).unwrap(),
                    "^",
                    expected,
                    indent = col - 1
                ),
                ParseError::EOF { expected } => write!(f, "Unexpected end of file, expected {}", expected),
                ParseError::Fixity { found, prefix, row, col, code: _ } => write!(
                    f,
                    "{:?} is not a {}fix operator, at {}:{}:\n{}\n{: >indent$}",
                    found,
                    if *prefix { "pre" } else { "in" },
                    row,
                    col,
                    "TODO",
                    // code.lines().nth(*row - 1).unwrap(),
                    "^",
                    indent = col - 1
                ),
            }
        }
    }

    impl Debug for ParseError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for ParseError {}
}
