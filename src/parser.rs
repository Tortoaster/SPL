use std::fmt;
use std::iter::Peekable;

use crate::lexer::{Field, Lexer, Operator, Token};

pub type Result<T, E = ParseError> = std::result::Result<T, E>;
type ParseError = String;

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
            if tokens.peek() == Some(separator) {
                munch(tokens, separator)?;
            } else {
                break;
            }
        }
        Ok(parsed)
    }
}

pub fn munch(tokens: &mut Peekable<Lexer>, expected: &Token) -> Result<()> {
    let found = tokens.next().ok_or(String::from("Unexpected EOF"))?;

    if found == *expected {
        Ok(())
    } else {
        Err(format!("Bad token: expected {:?} found {:?}", expected, found))
    }
}

/*
Grammar
 */

pub struct SPL(Vec<Decl>);

pub enum Decl {
    VarDecl(VarDecl),
    FunDecl(FunDecl),
}

pub struct VarDecl(VarType, Id, Exp);

pub enum VarType {
    Var,
    Type(Type),
}

pub struct FunDecl(Id, Vec<Id>, Option<FunType>, Vec<VarDecl>, Vec<Stmt>);

pub struct FunType(Vec<Type>, RetType);

pub enum RetType {
    Type(Type),
    Void,
}

pub enum Type {
    BasicType(BasicType),
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Generic(Id),
}

pub enum BasicType {
    Int,
    Bool,
    Char,
}

pub enum Stmt {
    If(Exp, Vec<Stmt>, Vec<Stmt>),
    While(Exp, Vec<Stmt>),
    Assignment(Id, Selector, Exp),
    FunCall(FunCall),
    Return(Option<Exp>),
}

pub enum Exp {
    Identifier(Id, Selector),
    BinaryOp(Operator, Box<Exp>, Box<Exp>),
    UnaryOp(Operator, Box<Exp>),
    Number(i32),
    Character(char),
    False,
    True,
    FunCall(FunCall),
    Nil,
    Tuple(Box<Exp>, Box<Exp>),
}

pub struct Selector(Vec<Field>);

pub struct FunCall(Id, Vec<Exp>);

pub struct Id(String);

/*
Parser
 */

impl SPL {
    pub fn new(input: &str) -> Result<Self> {
        let mut lexer = Lexer::new(input).peekable();
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

        Ok(SPL(decls))
    }
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

impl Parsable for VarDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = VarType::parse(tokens)?;
        let id = Id::parse(tokens)?;
        munch(tokens, &Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        munch(tokens, &Token::Semicolon)?;

        Ok(VarDecl(var_type, id, exp))
    }
}

impl Parsable for FunDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let id = Id::parse(tokens)?;
        munch(tokens, &Token::OpenParen)?;
        let params = Id::parse_many_sep(tokens, &Token::Comma)?;
        munch(tokens, &Token::CloseParen)?;

        let fun_type = if tokens.peek() == Some(&Token::HasType) {
            munch(tokens, &Token::HasType)?;
            Some(FunType::parse(tokens)?)
        } else {
            None
        };

        munch(tokens, &Token::OpenBracket)?;
        let var_decls = VarDecl::parse_many(tokens);
        let stmts = Stmt::parse_many(tokens);
        munch(tokens, &Token::CloseBracket)?;

        Ok(FunDecl(id, params, fun_type, var_decls, stmts))
    }
}

impl Parsable for VarType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::Var => {
                munch(tokens, &Token::Var)?;
                VarType::Var
            },
            _ => VarType::Type(Type::parse(tokens)?)
        };

        Ok(var_type)
    }
}

impl Parsable for RetType {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let ret_type = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
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
        let args = Type::parse_many(tokens);
        munch(tokens, &Token::To)?;
        let ret = RetType::parse(tokens)?;
        Ok(FunType(args, ret))
    }
}

impl Parsable for Type {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let t = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
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
        let t = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Int => BasicType::Int,
            Token::Bool => BasicType::Bool,
            Token::Char => BasicType::Char,
            t => return Err(format!("Bad token: expected Int, Bool, or Char, found {:?}", t))
        };

        Ok(t)
    }
}

impl Parsable for Stmt {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        let t = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::If => {
                munch(tokens, &Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                munch(tokens, &Token::CloseParen)?;
                munch(tokens, &Token::OpenBracket)?;
                let then = Stmt::parse_many(tokens);
                munch(tokens, &Token::CloseBracket)?;
                let otherwise = if tokens.peek() == Some(&Token::Else) {
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
            Token::While => {
                munch(tokens, &Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                munch(tokens, &Token::CloseParen)?;
                munch(tokens, &Token::OpenBracket)?;
                let repeat = Stmt::parse_many(tokens);
                munch(tokens, &Token::CloseBracket)?;

                Stmt::While(condition, repeat)
            }
            Token::Return => {
                let value = if tokens.peek() == Some(&Token::Semicolon) {
                    None
                } else {
                    Some(Exp::parse(tokens)?)
                };
                munch(tokens, &Token::Semicolon)?;

                Stmt::Return(value)
            }
            Token::Identifier(s) => {
                let id = Id(s);
                if tokens.peek() == Some(&Token::OpenParen) {
                    munch(tokens, &Token::OpenParen)?;
                    let args = Exp::parse_many_sep(tokens, &Token::Comma)?;
                    munch(tokens, &Token::CloseParen)?;
                    munch(tokens, &Token::Semicolon)?;

                    Stmt::FunCall(FunCall(id, args))
                } else {
                    let selector = Selector::parse(tokens)?;
                    munch(tokens, &Token::Assign)?;
                    let exp = Exp::parse(tokens)?;
                    munch(tokens, &Token::Semicolon)?;

                    Stmt::Assignment(id, selector, exp)
                }
            }
            t => return Err(format!("Bad token: expected Int, Bool, or Char, found {:?}", t))
        };

        Ok(t)
    }
}

impl Exp {
    fn parse_exp(tokens: &mut Peekable<Lexer>, min_bp: u8) -> Result<Self> {
        let mut lhs = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(s) => {
                let id = Id(s);
                if tokens.peek() == Some(&Token::OpenParen) {
                    munch(tokens, &Token::OpenParen)?;
                    let fun_call = FunCall(id, Exp::parse_many_sep(tokens, &Token::Comma)?);
                    munch(tokens, &Token::CloseParen)?;
                    Exp::FunCall(fun_call)
                } else {
                    Exp::Identifier(id, Selector::parse(tokens)?)
                }
            }
            Token::Operator(op) => {
                let r_bp = op.prefix_binding_power()?;
                let rhs = Self::parse_exp(tokens, r_bp)?;
                Exp::UnaryOp(op.clone(), Box::new(rhs))
            }
            Token::Number(n) => Exp::Number(n),
            Token::Character(c) => Exp::Character(c),
            Token::False => Exp::False,
            Token::True => Exp::True,
            Token::OpenParen => {
                let lhs = Self::parse_exp(tokens, 0)?;
                if tokens.peek() == Some(&Token::CloseParen) {
                    munch(tokens, &Token::CloseParen)?;
                    lhs
                } else {
                    munch(tokens, &Token::Comma)?;
                    let rhs = Self::parse_exp(tokens, 0)?;
                    munch(tokens, &Token::CloseParen)?;
                    Exp::Tuple(Box::new(lhs), Box::new(rhs))
                }
            }
            Token::Nil => Exp::Nil,
            t => return Err(format!("Bad token: {:?}", t)),
        };

        loop {
            let op = match tokens.peek() {
                Some(Token::Operator(op)) => op.clone(),
                _ => break,
            };

            let (l_bp, r_bp) = op.infix_binding_power()?;

            if l_bp < min_bp {
                break;
            }

            tokens.next();
            let rhs = Self::parse_exp(tokens, r_bp)?;

            lhs = Exp::BinaryOp(op, Box::new(lhs), Box::new(rhs));
        }

        Ok(lhs)
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

impl Parsable for Exp {
    fn parse(lexer: &mut Peekable<Lexer>) -> Result<Self> {
        Self::parse_exp(lexer, 0)
    }
}

impl Parsable for Selector {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        let mut fields = Vec::new();

        while let Some(Token::Dot) = tokens.peek() {
            munch(tokens, &Token::Dot)?;
            match tokens.next().ok_or(String::from("Unexpected EOF"))? {
                Token::Field(f) => fields.push(f),
                t => return Err(format!("Bad token: expected field, found {:?}", t))
            }
        }

        Ok(Selector(fields))
    }
}

impl Parsable for Id {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(s) => Ok(Id(s)),
            t => return Err(format!("Bad token: expected identifier, found {:?}", t))
        }
    }
}

/*
Pretty printer
 */

impl fmt::Display for SPL {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for decl in &self.0 {
            writeln!(f, "{}", decl)?;
        }
        Ok(())
    }
}

impl fmt::Display for Decl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Decl::VarDecl(var) => write!(f, "{}", var),
            Decl::FunDecl(fun) => write!(f, "{}", fun),
        }
    }
}

impl fmt::Display for VarDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {} = {};", self.0, self.1, self.2)
    }
}

impl fmt::Display for VarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VarType::Var => write!(f, "var"),
            VarType::Type(t) => write!(f, "{}", t),
        }
    }
}

impl fmt::Display for FunDecl {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.0)?;
        for id in &self.1 {
            write!(f, "{}, ", id)?;
        }
        write!(f, ") ")?;
        if let Some(fun_type) = &self.2 {
            write!(f, "{} ", fun_type)?;
        }
        writeln!(f, "{{")?;
        for var in &self.3 {
            writeln!(f, "\t{}", var)?;
        }
        for stmt in &self.4 {
            writeln!(f, "\t{}", stmt)?;
        }
        write!(f, "}}")
    }
}

impl fmt::Display for FunType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, ":: ")?;
        for t in &self.0 {
            write!(f, "{} ", t)?;
        }
        write!(f, "-> {}", self.1)
    }
}

impl fmt::Display for RetType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RetType::Type(t) => write!(f, "{}", t),
            RetType::Void => write!(f, "Void"),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::BasicType(t) => write!(f, "{}", t),
            Type::Tuple(l, r) => write!(f, "({}, {})", l, r),
            Type::Array(t) => write!(f, "[{}]", t),
            Type::Generic(t) => write!(f, "{}", t),
        }
    }
}

impl fmt::Display for BasicType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BasicType::Int => write!(f, "Int"),
            BasicType::Bool => write!(f, "Bool"),
            BasicType::Char => write!(f, "Char"),
        }
    }
}

impl fmt::Display for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Stmt::If(condition, then, otherwise) => {
                writeln!(f, "if ({}) {{", condition)?;
                for stmt in then {
                    writeln!(f, "\t{}", stmt)?;
                }
                if otherwise.is_empty() {
                    writeln!(f, "}}")
                } else {
                    writeln!(f, "}} else {{")?;
                    for stmt in otherwise {
                        writeln!(f, "\t{}", stmt)?;
                    }
                    write!(f, "}}")
                }
            }
            Stmt::While(condition, body) => {
                writeln!(f, "while ({}) {{", condition)?;
                for stmt in body {
                    writeln!(f, "\t{}", stmt)?;
                }
                write!(f, "}}")
            },
            Stmt::Assignment(id, field, value) => write!(f, "{}{} = {};", id, field, value),
            Stmt::FunCall(fun_call) => write!(f, "{};", fun_call),
            Stmt::Return(value) => match value {
                None => write!(f, "return;"),
                Some(ret) => write!(f, "return {};", ret),
            }
        }
    }
}

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Exp::Identifier(id, selector) => write!(f, "{}{}", id, selector),
            Exp::BinaryOp(op, lhs, rhs) => write!(f, "{} {} {}", lhs, op, rhs),
            Exp::UnaryOp(op, lhs) => write!(f, "{}{}", op, lhs),
            Exp::Number(n) => write!(f, "{}", n),
            Exp::Character(c) => write!(f, "{}", c),
            Exp::False => write!(f, "False"),
            Exp::True => write!(f, "True"),
            Exp::FunCall(fun_call) => write!(f, "{}", fun_call),
            Exp::Nil => write!(f, "[]"),
            Exp::Tuple(l, r) => write!(f, "({}, {})", l, r),
        }
    }
}

impl fmt::Display for Selector {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for field in &self.0 {
            write!(f, ".{}", field)?;
        }
        Ok(())
    }
}

impl fmt::Display for FunCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}(", self.0)?;
        for exp in &self.1 {
            write!(f, "{}, ", exp)?;
        }
        write!(f, ")")
    }
}

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}
