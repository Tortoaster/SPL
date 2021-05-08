use std::collections::{BTreeMap, HashMap};
use std::iter::Peekable;

use error::Result;

use crate::algorithm_w::{Environment, Generator, Type, TypeClass, TypeVariable};
use crate::char_iterator::Positioned;
use crate::lexer::{Field, Lexer, Operator, Token};
use crate::parser::error::ParseError;
use crate::tree::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};

trait Consume {
    fn munch<T: AsRef<Token>>(&mut self, expected: T) -> Result<()>;
}

impl Consume for Peekable<Lexer<'_>> {
    fn munch<T: AsRef<Token>>(&mut self, expected: T) -> Result<()> {
        let found = self.next().ok_or(ParseError::EOF { expected: format!("{:?}", expected.as_ref()) })?;

        if *found == *expected.as_ref() {
            Ok(())
        } else {
            Err(found.into_bad_token_err(format!("{:?}", expected.as_ref())))
        }
    }
}

pub trait Parsable: Sized {
    /// Parses this parsable. This consumes the necessary tokens from the iterator,
    /// hence this should only be used when no alternative parsables are valid.
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self>;

    /// Tries to parse this parsable. If it succeeds, this returns the same value as parse,
    /// but if it fails, this function won't advance the iterator (at the cost of performance).
    fn try_parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut copy = (*tokens).clone();
        let parsed = Self::parse(&mut copy)?;
        *tokens = copy;
        Ok(parsed)
    }

    /// Parses as many instances of this parsable after each other as possible.
    fn parse_many(tokens: &mut Peekable<Lexer>) -> Vec<Self> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
        }
        parsed
    }

    /// Parses as many instances of this parsable after each other as possible, separated by separator.
    fn parse_many_sep<T: AsRef<Token>>(tokens: &mut Peekable<Lexer>, separator: T) -> Result<Vec<Self>> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
            match tokens.peek() {
                None => break,
                Some(s) => if *separator.as_ref() != **s { break; }
            }
            tokens.munch(&separator)?;
        }
        Ok(parsed)
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
        let var_type = <Option<Type>>::parse(tokens)?;
        let id = Id::parse(tokens)?;
        tokens.munch(Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        tokens.munch(Token::Semicolon)?;

        Ok(VarDecl { var_type, id, exp })
    }
}

impl Parsable for FunDecl {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let id = Id::parse(tokens)?;
        tokens.munch(Token::OpenParen)?;
        let args = Id::parse_many_sep(tokens, Token::Comma)?;
        tokens.munch(Token::CloseParen)?;

        let fun_type = if let Some(Positioned { inner: Token::HasType, .. }) = tokens.peek() {
            tokens.munch(Token::HasType)?;
            Some(Type::parse_function(tokens, &mut Generator::new(), &mut HashMap::new())?.generalize(&Environment::new()))
        } else {
            None
        };

        tokens.munch(Token::OpenBracket)?;
        let var_decls = VarDecl::parse_many(tokens);
        let stmts = Stmt::parse_many(tokens);
        tokens.munch(Token::CloseBracket)?;

        Ok(FunDecl { id, args, fun_type, var_decls, stmts })
    }
}

/// Parsable for variable type annotations
impl Parsable for Option<Type> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match **tokens.peek().ok_or(ParseError::EOF { expected: "variable type".to_owned() })? {
            Token::Var => {
                tokens.munch(Token::Var)?;
                Ok(None)
            }
            _ => {
                let parsed = Type::parse_basic(tokens, &mut Generator::new(), &mut HashMap::new())?;
                match parsed {
                    Type::Int | Type::Bool | Type::Char | Type::Tuple(_, _) | Type::Array(_) => Ok(Some(parsed)),
                    Type::Polymorphic(_) => Err(ParseError::PolyVar),
                    _ => Err(ParseError::InvalidAnnotation)
                }
            }
        }
    }
}

/// Parsable for many type class annotations
impl Parsable for Vec<(TypeClass, Id)> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let type_classes = <(TypeClass, Id)>::parse_many_sep(tokens, Token::Comma)?;
        tokens.munch(Token::DoubleArrow)?;
        Ok(type_classes)
    }
}

/// Parsable for type class annotations
impl Parsable for (TypeClass, Id) {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let class = match Id::parse(tokens)?.0.as_str() {
            "Any" => TypeClass::Any,
            "Show" => TypeClass::Show,
            "Eq" => TypeClass::Eq,
            "Ord" => TypeClass::Ord,
            _ => return Err(ParseError::InvalidAnnotation)
        };
        let var = Id::parse(tokens)?;

        Ok((class, var))
    }
}

impl AsRef<Token> for Token {
    fn as_ref(&self) -> &Token {
        &self
    }
}

impl Type {
    /// Parses any type other than a function
    fn parse_basic(tokens: &mut Peekable<Lexer>, gen: &mut Generator, poly_names: &mut HashMap<Id, TypeVariable>) -> Result<Self> {
        let token = tokens.peek().ok_or(ParseError::EOF { expected: "type".to_owned() })?;
        let t = match **token {
            Token::Void => {
                tokens.munch(Token::Void)?;
                Type::Void
            }
            Token::Int => {
                tokens.munch(Token::Int)?;
                Type::Int
            }
            Token::Bool => {
                tokens.munch(Token::Bool)?;
                Type::Bool
            }
            Token::Char => {
                tokens.munch(Token::Char)?;
                Type::Char
            }
            Token::OpenParen => {
                tokens.munch(Token::OpenParen)?;
                let l = Type::parse_basic(tokens, gen, poly_names)?;
                tokens.munch(Token::Comma)?;
                let r = Type::parse_basic(tokens, gen, poly_names)?;
                tokens.munch(Token::CloseParen)?;
                Type::Tuple(Box::new(l), Box::new(r))
            }
            Token::OpenArr => {
                tokens.munch(Token::OpenArr)?;
                let t = Type::parse_basic(tokens, gen, poly_names)?;
                tokens.munch(Token::CloseArr)?;
                Type::Array(Box::new(t))
            }
            Token::Identifier(_) => {
                let id = Id::parse(tokens)?;
                Type::Polymorphic(poly_names.entry(id).or_insert(gen.fresh()).clone())
            }
            _ => return Err(token.clone().into_bad_token_err("type"))
        };

        Ok(t)
    }

    /// Parses a function type, including type class constraints
    pub fn parse_function(tokens: &mut Peekable<Lexer>, gen: &mut Generator, poly_names: &mut HashMap<Id, TypeVariable>) -> Result<Self> {
        // Read optional type class constraints
        let type_classes = <Vec<(TypeClass, Id)>>::try_parse(tokens).unwrap_or(Vec::new());
        for (class, var) in type_classes {
            poly_names.entry(var).or_insert(gen.fresh()).impose(class);
        }

        let mut arg_types = Vec::new();
        loop {
            let token = tokens.peek().ok_or(ParseError::EOF { expected: "type".to_owned() })?;
            match **token {
                Token::To => break,
                _ => arg_types.push(Type::parse_basic(tokens, gen, poly_names)?)
            }
        }
        tokens.munch(Token::To)?;
        let ret_type = Type::parse_basic(tokens, gen, poly_names)?;
        let fun_type = arg_types
            .into_iter()
            .rfold(ret_type, |res, arg| Type::Function(Box::new(arg), Box::new(res)));

        Ok(fun_type)
    }
}

impl Parsable for Stmt {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self, ParseError> {
        let token = tokens.next().ok_or(ParseError::EOF { expected: "statement".to_owned() })?;
        let t = match &*token {
            Token::If => {
                tokens.munch(Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                tokens.munch(Token::CloseParen)?;
                tokens.munch(Token::OpenBracket)?;
                let then = Stmt::parse_many(tokens);
                tokens.munch(Token::CloseBracket)?;
                let otherwise = if let Some(Positioned { inner: Token::Else, .. }) = tokens.peek() {
                    tokens.munch(Token::Else)?;
                    tokens.munch(Token::OpenBracket)?;
                    let result = Stmt::parse_many(tokens);
                    tokens.munch(Token::CloseBracket)?;
                    result
                } else {
                    Vec::new()
                };

                Stmt::If(condition, then, otherwise)
            }
            Token::While => {
                tokens.munch(Token::OpenParen)?;
                let condition = Exp::parse(tokens)?;
                tokens.munch(Token::CloseParen)?;
                tokens.munch(Token::OpenBracket)?;
                let repeat = Stmt::parse_many(tokens);
                tokens.munch(Token::CloseBracket)?;

                Stmt::While(condition, repeat)
            }
            Token::Return => {
                let value = if let Some(Positioned { inner: Token::Semicolon, .. }) = tokens.peek() {
                    None
                } else {
                    Some(Exp::parse(tokens)?)
                };
                tokens.munch(Token::Semicolon)?;

                Stmt::Return(value)
            }
            Token::Identifier(s) => {
                let id = Id(s.clone());
                if let Some(Positioned { inner: Token::OpenParen, .. }) = tokens.peek() {
                    tokens.munch(Token::OpenParen)?;
                    let args = Exp::parse_many_sep(tokens, Token::Comma)?;
                    tokens.munch(Token::CloseParen)?;
                    tokens.munch(Token::Semicolon)?;

                    Stmt::FunCall(FunCall { id, args, type_args: BTreeMap::new() })
                } else {
                    let selector = <Vec<Field>>::parse(tokens)?;
                    tokens.munch(Token::Assign)?;
                    let exp = Exp::parse(tokens)?;
                    tokens.munch(Token::Semicolon)?;

                    Stmt::Assignment(id, selector, exp)
                }
            }
            _ => return Err(token.into_bad_token_err("statement"))
        };

        Ok(t)
    }
}

impl Exp {
    fn parse_exp(tokens: &mut Peekable<Lexer>, min_bp: u8) -> Result<Self> {
        let mut lhs = match tokens.next().ok_or(ParseError::EOF { expected: "expression".to_owned() })? {
            Positioned { inner: Token::Identifier(s), .. } => {
                let id = Id(s);
                if let Some(Positioned { inner: Token::OpenParen, .. }) = tokens.peek() {
                    tokens.munch(Token::OpenParen)?;
                    let fun_call = FunCall { id, args: Exp::parse_many_sep(tokens, Token::Comma)?, type_args: BTreeMap::new() };
                    tokens.munch(Token::CloseParen)?;
                    Exp::FunCall(fun_call)
                } else {
                    let fields = <Vec<Field>>::parse(tokens)?;
                    fields.into_iter().fold(Exp::Variable(id), |e, f| Exp::FunCall(FunCall { id: Id(format!("{}", f)), args: vec![e], type_args: BTreeMap::new() }))
                }
            }
            Positioned { inner: Token::Operator(op), row, col, .. } => {
                let r_bp = op.prefix_binding_power(row, col)?;
                let rhs = Self::parse_exp(tokens, r_bp)?;
                Exp::FunCall(FunCall { id: op.prefix_id(row, col)?, args: vec![rhs], type_args: BTreeMap::new() })
            }
            Positioned { inner: Token::Number(n), .. } => Exp::Number(n),
            Positioned { inner: Token::Character(c), .. } => Exp::Character(c),
            Positioned { inner: Token::False, .. } => Exp::False,
            Positioned { inner: Token::True, .. } => Exp::True,
            Positioned { inner: Token::OpenParen, .. } => {
                let lhs = Self::parse_exp(tokens, 0)?;
                if let Some(Positioned { inner: Token::CloseParen, .. }) = tokens.peek() {
                    tokens.munch(Token::CloseParen)?;
                    lhs
                } else {
                    tokens.munch(Token::Comma)?;
                    let rhs = Self::parse_exp(tokens, 0)?;
                    tokens.munch(Token::CloseParen)?;
                    Exp::Tuple(Box::new(lhs), Box::new(rhs))
                }
            }
            Positioned { inner: Token::Nil, .. } => Exp::Nil,
            token => return Err(token.transform(ParseError::BadToken {
                found: token.inner,
                expected: "expression".to_owned()
            }))
        };

        while let Some(Positioned { inner: Token::Operator(op), row, col, .. }) = tokens.peek() {
            let (l_bp, r_bp) = op.infix_binding_power(*row, *col)?;

            if l_bp < min_bp {
                break;
            }

            let op = tokens.next().unwrap().transform(op);
            let rhs = Self::parse_exp(tokens, r_bp)?;

            lhs = Exp::FunCall(FunCall { id: op.infix_id()?, args: vec![lhs, rhs], type_args: BTreeMap::new() });
        }

        Ok(lhs)
    }
}

impl Positioned<Operator> {
    fn prefix_binding_power(&self) -> Result<u8> {
        let bp = match self.inner {
            Operator::Minus => 17,
            Operator::Not => 7,
            _ => return Err(self.transform(ParseError::Fixity {
                found: self.inner.clone(),
                prefix: true
            }))
        };

        Ok(bp)
    }

    fn infix_binding_power(&self) -> Result<(u8, u8)> {
        let bp = match self.inner {
            Operator::Times | Operator::Divide | Operator::Modulo => (15, 16),
            Operator::Plus | Operator::Minus => (13, 14),
            Operator::Smaller | Operator::Greater |
            Operator::SmallerEqual | Operator::GreaterEqual => (11, 12),
            Operator::Equals | Operator::NotEqual => (9, 10),
            Operator::And => (6, 5),
            Operator::Or => (4, 3),
            Operator::Cons => (2, 1),
            _ => return Err(self.transform(ParseError::Fixity {
                found: self.inner.clone(),
                prefix: false
            }))
        };

        Ok(bp)
    }

    pub fn prefix_id(&self) -> Result<Id> {
        let name = match self.inner {
            Operator::Not => "not",
            Operator::Minus => "neg",
            _ => return Err(self.transform(ParseError::Fixity {
                found: self.inner.clone(),
                prefix: true
            }))
        };

        Ok(Id(name.to_owned()))
    }

    pub fn infix_id(&self) -> Result<Id> {
        let name = match self.inner {
            Operator::Plus => "add",
            Operator::Minus => "sub",
            Operator::Times => "mul",
            Operator::Divide => "div",
            Operator::Modulo => "mod",
            Operator::Equals => "eq",
            Operator::NotEqual => "ne",
            Operator::Smaller => "lt",
            Operator::Greater => "gt",
            Operator::SmallerEqual => "le",
            Operator::GreaterEqual => "ge",
            Operator::And => "and",
            Operator::Or => "or",
            Operator::Cons => "cons",
            _ => return Err(self.transform(ParseError::Fixity {
                found: self.inner.clone(),
                prefix: false
            }))
        };

        Ok(Id(name.to_owned()))
    }
}

impl Parsable for Exp {
    fn parse(lexer: &mut Peekable<Lexer>) -> Result<Self> {
        Self::parse_exp(lexer, 0)
    }
}

impl Parsable for Vec<Field> {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        let mut fields = Vec::new();

        while let Some(Positioned { inner: Token::Field(_), .. }) = tokens.peek() {
            match tokens.next() {
                Some(Positioned { inner: Token::Field(field), .. }) => fields.push(field),
                _ => panic!("Impossible")
            }
        }

        Ok(fields)
    }
}

impl Parsable for Id {
    fn parse(tokens: &mut Peekable<Lexer>) -> Result<Self> {
        match tokens.next().ok_or(ParseError::EOF { expected: "identifier".to_owned() })? {
            Positioned { inner: Token::Identifier(s), .. } => Ok(Id(s)),
            token => Err(token.transform(ParseError::BadToken {
                found: token.inner,
                expected: "identifier".to_owned()
            }))
        }
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::char_iterator::Positioned;
    use crate::lexer::{Operator, Token};

    pub type Result<T, E = Positioned<ParseError>> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum ParseError {
        BadToken {
            found: Token,
            expected: String,
        },
        EOF {
            expected: String
        },
        Fixity {
            found: Operator,
            prefix: bool,
        },
        InvalidAnnotation,
        PolyVar,
    }

    impl fmt::Display for Positioned<ParseError> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                Positioned { inner: ParseError::BadToken { found, expected }, row, col, code } => write!(
                    f,
                    "Bad token {:?} at {}:{}:\n{}\n{: >indent$}\nExpected: {}",
                    found,
                    row,
                    col,
                    code.lines().nth(*row - 1).unwrap(),
                    "^",
                    expected,
                    indent = col - 1
                ),
                Positioned { inner: ParseError::EOF { expected }, .. } => write!(f, "Unexpected end of file, expected {}", expected),
                Positioned { inner: ParseError::Fixity { found, prefix }, row, col, code } => write!(
                    f,
                    "{:?} is not a{}fix operator, at {}:{}:\n{}\n{: >indent$}",
                    found,
                    if *prefix { " pre" } else { "n in" },
                    row,
                    col,
                    code.lines().nth(*row - 1).unwrap(),
                    "^",
                    indent = col - 1
                ),
                Positioned { inner: ParseError::InvalidAnnotation, .. } => write!(f, "Variables cannot have a function or void type"),
                Positioned { inner: ParseError::PolyVar, .. } => write!(f, "Use the 'var' keyword to indicate a polymorphic variable")
            }
        }
    }

    impl Debug for Positioned<ParseError> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for Positioned<ParseError> {}
}
