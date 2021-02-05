use std::fmt;
use crate::lexer::{Lexer, Token, Operator};
use std::iter::Peekable;
use crate::lexer::Token::Terminal;

pub type Result<T, E = ParseError> = std::result::Result<T, E>;
type ParseError = String;

trait Parsable: Sized {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self>;

    /**
    Tries to parse this parsable. If it succeeds, this returns the same value as parse,
    but if it fails, this function won't advance the iterator (at the cost of performance)
    **/
    fn try_parse(mut tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut copy = (*tokens).clone();
        let parsed = Self::parse(&mut copy)?;
        *tokens = copy;
        Ok(parsed)
    }

    fn parse_many(mut tokens: &mut Peekable<Lexer>) -> Vec<Self> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
        }
        parsed
    }
}

pub struct SPL(Vec<Decl>);

impl SPL {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input).peekable();
        Self::parse(&mut lexer)
    }
}

impl Parsable for SPL {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut decls = Vec::new();

        while let Ok(d) = Decl::parse(tokens) {
            decls.push(d);
        }

        Ok(SPL(decls))
    }
}

pub enum Decl {
    VarDecl(VarDecl),
    FunDecl(FunDecl)
}

impl Parsable for Decl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let decl = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(_) => Decl::FunDecl(FunDecl::parse(tokens)?),
            _ => Decl::VarDecl(VarDecl::parse(tokens)?)
        };

        Ok(decl)
    }
}

pub struct VarDecl(VarType, Id, Exp);

impl Parsable for VarDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = VarType::parse(tokens)?;
        let id = Id::parse(tokens)?;
        munch(tokens, Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        munch(tokens, Token::Terminal)?;

        Ok(VarDecl(var_type, id, exp))
    }
}

pub struct FunDecl(Id, Vec<Id>, Option<FunType>, Vec<VarDecl>, Vec<Stmt>);

impl Parsable for FunDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let id = Id::parse(tokens)?;
        munch(tokens, Token::OpenParen)?;
        let mut params = Id::parse_many(tokens);
        munch(tokens, Token::CloseParen)?;

        let fun_type = if tokens.peek() == Some(&Token::HasType) {
            Some(FunType::parse(tokens)?)
        } else {
            None
        };

        munch(tokens, Token::OpenBracket)?;
        let mut var_decls = VarDecl::parse_many(tokens);
        let mut stmts = Stmt::parse_many(tokens);
        munch(tokens, Token::CloseBracket)?;

        Ok(FunDecl(id, params, fun_type, var_decls, stmts))
    }
}

pub enum VarType { Var, Type(Type) }

impl Parsable for VarType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::Var => Ok(VarType::Var),
            _ => Ok(VarType::Type(Type::parse(tokens)?))
        }
    }
}

pub enum RetType {
    Type(Type),
    Void
}

impl Parsable for RetType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let ret_type = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::Void => {
                tokens.next();
                RetType::Void
            },
            _ => RetType::Type(Type::parse(tokens)?)
        };

        Ok(ret_type)
    }
}

pub struct FunType(Vec<Type>, RetType);

impl Parsable for FunType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let args = Type::parse_many(tokens);
        munch(tokens, Token::To)?;
        let ret = RetType::parse(tokens)?;
        Ok(FunType(args, ret))
    }
}

pub enum Type {
    BasicType(BasicType),
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Generic(String)
}

impl Parsable for Type {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let t = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Int => Type::BasicType(BasicType::Int),
            Token::Bool => Type::BasicType(BasicType::Bool),
            Token::Char => Type::BasicType(BasicType::Char),
            Token::OpenParen => {
                let l = Type::parse(tokens)?;
                munch(tokens, Token::Separator)?;
                let r = Type::parse(tokens)?;
                munch(tokens, Token::CloseArr)?;
                Type::Tuple(Box::new(l), Box::new(r))
            }
            Token::OpenArr => {
                let t = Type::parse(tokens)?;
                munch(tokens, Token::CloseArr)?;
                t
            }
            Token::Identifier(s) => Type::Generic(s),
            t => return Err(format!("Bad token: expected type, found {:?}", t))
        };

        Ok(t)
    }
}

pub enum BasicType {
    Int,
    Bool,
    Char,
}

pub enum Stmt {
    If(Exp, Vec<Stmt>, Vec<Stmt>),
    While(Exp, Vec<Stmt>),
    Assignment(Id, Field, Exp),
    FunCall(FunCall),
    Return(Option<Exp>),
}

impl Parsable for Stmt {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::If => {
                munch(tokens, Token::If)?;
                munch(tokens, Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                munch(tokens, Token::CloseParen)?;
                munch(tokens, Token::OpenBracket)?;
                let then = Stmt::parse_many(tokens);
                munch(tokens, Token::CloseBracket)?;
                let mut otherwise = Vec::new();
                if tokens.peek() == Some(&Token::Else) {
                    munch(tokens, Token::Else)?;
                    munch(tokens, Token::OpenBracket)?;
                    otherwise = Stmt::parse_many(tokens);
                    munch(tokens, Token::CloseBracket)?;
                }
                Ok(Stmt::If(condition, then, otherwise))
            }
            Token::While => {
                munch(tokens, Token::While);
                munch(tokens, Token::OpenParen);
                let condition = Exp::parse(tokens)?;
                munch(tokens, Token::CloseParen)?;
                munch(tokens, Token::OpenBracket)?;
                let repeat = Stmt::parse_many(tokens);
                munch(tokens, Token::CloseBracket)?;
                Ok(Stmt::While(condition, repeat))
            }
            Token::Return => {
                munch(tokens, Token::Return);
                let value = if tokens.peek() == Some(&Token::Terminal) {
                    None
                } else {
                    Some(Exp::parse(tokens)?)
                };
                munch(tokens, Token::Terminal)?;
                Ok(Stmt::Return(value))
            }
            _ => {
                if let Ok(f) = FunCall::try_parse(tokens) {
                    Ok(Stmt::FunCall(f))
                } else {
                    let id = Id::parse(tokens)?;
                    let field = Field::parse(tokens)?;
                    munch(tokens, Token::Assign)?;
                    let exp = Exp::parse(tokens)?;
                    munch(tokens, Token::Terminal)?;
                    Ok(Stmt::Assignment(id, field, exp))
                }
            }
        }
    }
}

pub enum Exp {
    Identifier(String, Field),
    Op(Operator, Vec<Exp>),
    Number(i32),
    Character(char),
    False,
    True,
    FunCall(FunCall),
    Nil,
    Tuple(Box<Exp>, Box<Exp>),
}

impl Parsable for Id {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(s) => Ok(Id(s)),
            t => return Err(format!("Bad token: expected identifier, found {:?}", t))
        }
    }
}

impl Exp {
    fn parse_exp(tokens: &mut Peekable<Lexer>, min_bp: u8) -> Result<Self> {
        let mut lhs = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(id) => Exp::Identifier(id, Field::parse(tokens)?),
            Token::Operator(op) => {
                let r_bp = op.prefix_binding_power()?;
                let rhs = Self::parse_exp(tokens, r_bp)?;
                Exp::Op(op.clone(), vec![rhs])
            }
            Token::Number(n) => Exp::Number(n),
            Token::Character(c) => Exp::Character(c),
            Token::False => Exp::False,
            Token::True => Exp::True,
            Token::OpenParen => {
                let lhs = Self::parse_exp(tokens, 0)?;
                if tokens.next() != Some(Token::CloseParen) {
                    return Err(String::from("Missing closing parentheses"));
                }
                lhs
            }
            Token::Nil => Exp::Nil,
            t => return Err(format!("Bad token: {:?}", t)),
        };

        loop {
            let op = match tokens.peek() {
                None => break,
                Some(Token::CloseParen) => break,
                Some(Token::Operator(op)) => op.clone(),
                t => return Err(format!("Bad token: {:?}", t)),
            };

            let (l_bp, r_bp) = op.infix_binding_power()?;

            if l_bp < min_bp {
                break;
            }

            tokens.next();
            let rhs = Self::parse_exp(tokens, r_bp)?;

            lhs = Exp::Op(op, vec![lhs, rhs]);
        }

        Ok(lhs)
    }
}

impl Parsable for Exp {
    fn parse(lexer: &mut Peekable<Lexer>) -> Result<Self> {
        let exp = Self::parse_exp(lexer, 0)?;

        match lexer.peek() {
            None => Ok(exp),
            Some(t) => match t {
                Token::CloseParen => Err(String::from("Too many closing parentheses")),
                _ => Err(String::from("Could not parse entire input"))
            }
        }
    }
}

pub struct Field;

impl Parsable for Field {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        unimplemented!()
    }
}

pub struct FunCall(String, Vec<Exp>);

impl Parsable for FunCall {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        unimplemented!()
    }
}

pub struct Id(String);

impl fmt::Display for SPL {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "SPL")
    }
}

impl Operator {
    fn prefix_binding_power(&self) -> Result<u8> {
        let bp = match self {
            Operator::Minus => 17,
            Operator::Not => 7,
            o => return Err(format!("{:?} is not a prefix operator", o))
        };

        Ok(bp)
    }

    fn infix_binding_power(&self) -> Result<(u8, u8)> {
        let bp = match self {
            Operator::Times | Operator::Divide | Operator::Modulo => (15, 16),
            Operator::Plus | Operator::Minus => (13, 14),
            Operator::Smaller | Operator::Greater |
            Operator::SmallerEqual | Operator::GreaterEqual => (11, 12),
            Operator::Equals | Operator::NotEqual => (9, 10),
            Operator::And => (6, 5),
            Operator::Or => (4, 3),
            Operator::Cons => (2, 1),
            o => return Err(format!("{:?} is not an infix operator", o))
        };

        Ok(bp)
    }
}

pub fn munch(tokens: &mut Peekable<Lexer>, expected: Token) -> Result<()> {
    let found = tokens.next().ok_or(String::from("Unexpected EOF"))?;

    if found == expected {
        Ok(())
    } else {
        Err(format!("Bad token: expected {:?} found {:?}", expected, found))
    }
}
