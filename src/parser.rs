use std::iter::Peekable;

use crate::lexer::{Field, Lexer, Operator, Token};

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

fn munch(tokens: &mut Peekable<Lexer>, expected: &Token) -> Result<()> {
    let found = tokens.next().ok_or(String::from("Unexpected EOF"))?;

    if found == *expected {
        Ok(())
    } else {
        Err(format!("Bad token: expected {:?} found {:?}", expected, found))
    }
}

#[derive(Debug, Eq, PartialEq)]
pub struct SPL<'a>(pub Vec<Decl<'a>>);

#[derive(Debug, Eq, PartialEq)]
pub enum Decl<'a> {
    VarDecl(VarDecl<'a>),
    FunDecl(FunDecl<'a>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct VarDecl<'a>(VarType, pub Id, Exp<'a>);

#[derive(Debug, Eq, PartialEq)]
pub enum VarType {
    Var,
    Type(Type),
}

#[derive(Debug, Eq, PartialEq)]
pub struct FunDecl<'a>(pub Id, Vec<Id>, Option<FunType>, Vec<VarDecl<'a>>, Vec<Stmt<'a>>);

#[derive(Debug, Eq, PartialEq)]
pub struct FunType(Vec<Type>, RetType);

#[derive(Debug, Eq, PartialEq)]
pub enum RetType {
    Type(Type),
    Void,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Type {
    BasicType(BasicType),
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Generic(Id),
}

#[derive(Debug, Eq, PartialEq)]
pub enum BasicType {
    Int,
    Bool,
    Char,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Stmt<'a> {
    If(Exp<'a>, Vec<Stmt<'a>>, Vec<Stmt<'a>>),
    While(Exp<'a>, Vec<Stmt<'a>>),
    Assignment(Id, Selector, Exp<'a>),
    FunCall(FunCall<'a>),
    Return(Option<Exp<'a>>),
}

#[derive(Debug, Eq, PartialEq)]
pub enum Exp<'a> {
    Variable(Id, Selector, Option<&'a VarDecl<'a>>),
    BinaryOp(Operator, Box<Exp<'a>>, Box<Exp<'a>>),
    UnaryOp(Operator, Box<Exp<'a>>),
    Number(i32),
    Character(char),
    False,
    True,
    FunCall(FunCall<'a>, Option<&'a FunDecl<'a>>),
    Nil,
    Tuple(Box<Exp<'a>>, Box<Exp<'a>>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Selector(Vec<Field>);

#[derive(Debug, Eq, PartialEq)]
pub struct FunCall<'a>(Id, Vec<Exp<'a>>);

#[derive(Debug, Eq, PartialEq)]
pub struct Id(pub String);

impl SPL<'_> {
    pub fn new(mut lexer: Peekable<Lexer>) -> Result<Self> {
        Self::parse(&mut lexer)
    }
}

impl Parsable for SPL<'_> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut decls = Vec::new();

        while tokens.peek().is_some() {
            let d = Decl::parse(tokens)?;
            decls.push(d);
        }

        Ok(SPL(decls))
    }
}

impl Parsable for Decl<'_> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let decl = match tokens.peek().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(_) => Decl::FunDecl(FunDecl::parse(tokens)?),
            _ => Decl::VarDecl(VarDecl::parse(tokens)?)
        };

        Ok(decl)
    }
}

impl Parsable for VarDecl<'_> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let var_type = VarType::parse(tokens)?;
        let id = Id::parse(tokens)?;
        munch(tokens, &Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        munch(tokens, &Token::Semicolon)?;

        Ok(VarDecl(var_type, id, exp))
    }
}

impl Parsable for FunDecl<'_> {
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
            }
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

impl Parsable for Stmt<'_> {
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

impl Exp<'_> {
    fn parse_exp(tokens: &mut Peekable<Lexer>, min_bp: u8) -> Result<Self> {
        let mut lhs = match tokens.next().ok_or(String::from("Unexpected EOF"))? {
            Token::Identifier(s) => {
                let id = Id(s);
                if tokens.peek() == Some(&Token::OpenParen) {
                    munch(tokens, &Token::OpenParen)?;
                    let fun_call = FunCall(id, Exp::parse_many_sep(tokens, &Token::Comma)?);
                    munch(tokens, &Token::CloseParen)?;
                    Exp::FunCall(fun_call, None)
                } else {
                    Exp::Variable(id, Selector::parse(tokens)?, None)
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

        while let Some(Token::Operator(op)) = tokens.peek() {
            let (l_bp, r_bp) = op.infix_binding_power()?;

            if l_bp < min_bp {
                break;
            }

            let op = match tokens.next() {
                Some(Token::Operator(op)) => op,
                _ => panic!("Impossible"),
            };
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

impl Parsable for Exp<'_> {
    fn parse(lexer: &mut Peekable<Lexer>) -> Result<Self> {
        Self::parse_exp(lexer, 0)
    }
}

impl Parsable for Selector {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
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

type Result<T, E = ParseError> = std::result::Result<T, E>;
pub type ParseError = String;

mod printer {
    use std::fmt;

    use super::{BasicType, Decl, Exp, FunCall, FunDecl, FunType, Id, RetType, Selector, SPL, Stmt, Type, VarDecl, VarType};

    const TAB_SIZE: usize = 4;

    trait PrettyPrintable {
        fn fmt_pretty(&self, indent: usize) -> String;
    }

    impl fmt::Display for SPL<'_> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self.fmt_pretty(0))
        }
    }

    impl PrettyPrintable for SPL<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            self.0.iter().map(|decl| decl.fmt_pretty(indent)).collect::<Vec<String>>().join("\n")
        }
    }

    impl PrettyPrintable for Decl<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Decl::VarDecl(var) => var.fmt_pretty(indent),
                Decl::FunDecl(fun) => fun.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for VarDecl<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{:indent$}{} {} = {};\n",
                    "",
                    self.0.fmt_pretty(indent),
                    self.1.fmt_pretty(indent),
                    self.2.fmt_pretty(indent),
                    indent = indent * TAB_SIZE
            )
        }
    }

    impl PrettyPrintable for VarType {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                VarType::Var => String::from("var"),
                VarType::Type(t) => t.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for FunDecl<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            let mut f = format!("{:indent$}{}({}) ",
                                "",
                                self.0.fmt_pretty(indent),
                                self.1.iter().map(|id| id.fmt_pretty(indent)).collect::<Vec<String>>().join(", "),
                                indent = indent * TAB_SIZE
            );
            if let Some(fun_type) = &self.2 {
                f += fun_type.fmt_pretty(indent).as_str();
            }
            f += format!("{{\n").as_str();
            f += self.3.iter().map(|var| var.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f += self.4.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
        }
    }

    impl PrettyPrintable for FunType {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!(":: {}-> {} ",
                    self.0.iter().map(|t| t.fmt_pretty(indent) + " ").collect::<Vec<String>>().join(""),
                    self.1.fmt_pretty(indent)
            )
        }
    }

    impl PrettyPrintable for RetType {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                RetType::Type(t) => t.fmt_pretty(indent),
                RetType::Void => String::from("Void"),
            }
        }
    }

    impl PrettyPrintable for Type {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Type::BasicType(t) => t.fmt_pretty(indent),
                Type::Tuple(l, r) => format!("({}, {})", l.fmt_pretty(indent), r.fmt_pretty(indent)),
                Type::Array(t) => format!("[{}]", t.fmt_pretty(indent)),
                Type::Generic(t) => t.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for BasicType {
        fn fmt_pretty(&self, _: usize) -> String {
            match self {
                BasicType::Int => String::from("Int"),
                BasicType::Bool => String::from("Bool"),
                BasicType::Char => String::from("Char"),
            }
        }
    }

    impl PrettyPrintable for Stmt<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Stmt::If(condition, then, otherwise) => {
                    let mut f = format!("{:indent$}if ({}) {{\n",
                                        "",
                                        condition.fmt_pretty(indent),
                                        indent = indent * TAB_SIZE
                    );
                    f += then.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    if !otherwise.is_empty() {
                        f += format!("{:indent$}}} else {{\n", "", indent = indent * TAB_SIZE).as_str();
                        f += otherwise.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    }
                    f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
                }
                Stmt::While(condition, body) => {
                    let mut f = format!("{:indent$}while ({}) {{\n",
                                        "",
                                        condition.fmt_pretty(indent),
                                        indent = indent * TAB_SIZE
                    );
                    f += body.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
                }
                Stmt::Assignment(id, field, value) => format!("{:indent$}{}{} = {};\n",
                                                              "",
                                                              id.fmt_pretty(indent),
                                                              field.fmt_pretty(indent),
                                                              value.fmt_pretty(indent),
                                                              indent = indent * TAB_SIZE
                ),
                Stmt::FunCall(fun_call) => format!("{:indent$}{};\n",
                                                   "",
                                                   fun_call.fmt_pretty(indent),
                                                   indent = indent * TAB_SIZE
                ),
                Stmt::Return(value) => match value {
                    None => format!("{:indent$}return;\n", "", indent = indent * TAB_SIZE),
                    Some(ret) => format!("{:indent$}return {};\n", "", ret.fmt_pretty(indent), indent = indent * TAB_SIZE),
                }
            }
        }
    }

    impl PrettyPrintable for Exp<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Exp::Variable(id, selector, _) => format!("{}{}", id.fmt_pretty(indent), selector.fmt_pretty(indent)),
                Exp::BinaryOp(op, lhs, rhs) => format!("({} {} {})", lhs.fmt_pretty(indent), op, rhs.fmt_pretty(indent)),
                Exp::UnaryOp(op, lhs) => format!("({}{})", op, lhs.fmt_pretty(indent)),
                Exp::Number(n) => format!("{}", n),
                Exp::Character(c) => format!("'{}'", c),
                Exp::False => format!("False"),
                Exp::True => format!("True"),
                Exp::FunCall(fun_call, _) => format!("{}", fun_call.fmt_pretty(indent)),
                Exp::Nil => format!("[]"),
                Exp::Tuple(l, r) => format!("({}, {})", l.fmt_pretty(indent), r.fmt_pretty(indent)),
            }
        }
    }

    impl PrettyPrintable for Selector {
        fn fmt_pretty(&self, _: usize) -> String {
            self.0.iter().map(|field| ".".to_owned() + format!("{}", field).as_str()).collect::<Vec<String>>().join("")
        }
    }

    impl PrettyPrintable for FunCall<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{}({})",
                    self.0.fmt_pretty(indent),
                    self.1.iter().map(|exp| exp.fmt_pretty(indent)).collect::<Vec<String>>().join(", ")
            )
        }
    }

    impl PrettyPrintable for Id {
        fn fmt_pretty(&self, _: usize) -> String {
            self.0.clone()
        }
    }
}
