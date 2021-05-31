use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::Debug;

use error::Result;

use crate::lexer::{Field, Operator, PeekLexer, Token};
use crate::parser::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
use crate::parser::error::ParseError;
use crate::position::{Join, Pos};
use crate::typer::{Generator, PType, Substitution, Type, TypeClass, TypeVariable};

trait Util<'a> {
    fn next_or_eof<T: AsRef<str>>(&mut self, expected: T) -> Result<'a, Pos<'a, Token>>;

    fn peek_or_eof<T: AsRef<str>>(&mut self, expected: T) -> Result<'a, &Pos<'a, Token>>;

    fn consume<T: AsRef<Token>>(&mut self, expected: T) -> Result<'a, Pos<'a, Token>>;
}

impl<'a> Util<'a> for PeekLexer<'a> {
    fn next_or_eof<T: AsRef<str>>(&mut self, expected: T) -> Result<'a, Pos<'a, Token>> {
        self.next().ok_or(Pos::new(
            self.code.lines().count(),
            self.code.lines().last().unwrap_or("").len() + 1,
            self.code,
            ParseError::EOF { expected: format!("{:?}", expected.as_ref()) },
        ))
    }

    fn peek_or_eof<T: AsRef<str>>(&mut self, expected: T) -> Result<'a, &Pos<'a, Token>> {
        // TODO: Improve
        self.peek().ok_or(Pos::new(
            1,
            1,
            "",
            ParseError::EOF { expected: format!("{:?}", expected.as_ref()) },
        ))
    }

    fn consume<T: AsRef<Token>>(&mut self, expected: T) -> Result<'a, Pos<'a, Token>> {
        let token = self.next_or_eof(format!("{:?}", expected.as_ref()))?;

        if token.content == *expected.as_ref() {
            Ok(token)
        } else {
            let (pos, inner) = token.eject();
            Err(pos.with(ParseError::BadToken {
                found: inner,
                expected: format!("{:?}", expected.as_ref()),
            }))
        }
    }
}

pub trait Parsable<'a>: Sized + Clone + Debug {
    /// Parses this parsable. This consumes the necessary tokens from the iterator,
    /// hence this should only be used when no alternative parsables are valid.
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>>;

    /// Tries to parse this parsable. If it succeeds, this returns the same value as parse,
    /// but if it fails, this function won't advance the iterator (at the cost of performance).
    fn try_parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let mut copy = (*tokens).clone();
        let parsed = Self::parse(&mut copy)?;
        *tokens = copy;
        Ok(parsed)
    }

    /// Parses as many instances of this parsable after each other as possible.
    fn parse_many(tokens: &mut PeekLexer<'a>) -> Vec<Pos<'a, Self>> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
        }
        parsed
    }

    /// Parses as many instances of this parsable after each other as possible, separated by separator.
    fn parse_many_sep<T: AsRef<Token>>(tokens: &mut PeekLexer<'a>, separator: T) -> Result<'a, Vec<Pos<'a, Self>>> {
        let mut parsed = Vec::new();
        while let Ok(p) = Self::try_parse(tokens) {
            parsed.push(p);
            match tokens.peek() {
                None => break,
                Some(s) => if *separator.as_ref() != s.content { break; }
            }
            // TODO: Include?
            let _ = tokens.consume(&separator)?;
        }

        Ok(parsed)
    }
}

impl<'a> SPL<'a> {
    pub fn new(mut lexer: PeekLexer<'a>) -> Result<Box<Pos<'a, Self>>> {
        Ok(Box::new(Self::parse(&mut lexer)?))
    }
}

impl<'a> Parsable<'a> for SPL<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let mut decls = Vec::new();

        while tokens.peek().is_some() {
            let decl = Decl::parse(tokens)?;
            decls.push(decl);
        }

        // TODO: Improve
        let pos = decls.join_with(()).unwrap_or(Pos::new(
            0,
            0,
            tokens.code,
            (),
        ));

        Ok(pos.with(SPL { decls }))
    }
}

impl<'a> Parsable<'a> for Decl<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.peek_or_eof("declaration")?;
        let decl = match token.content {
            Token::Identifier(_) => {
                let fun_decl = FunDecl::parse(tokens)?;
                let (pos, inner) = fun_decl.eject();
                pos.with(Decl::FunDecl(inner))
            }
            _ => {
                let var_decl = VarDecl::parse(tokens)?;
                let (pos, inner) = var_decl.eject();
                pos.with(Decl::VarDecl(inner))
            }
        };

        Ok(decl)
    }
}

impl<'a> Parsable<'a> for VarDecl<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let var_type = <Option<PType>>::parse(tokens)?;
        let id = Id::parse(tokens)?;
        let equals = tokens.consume(Token::Assign)?;
        let exp = Exp::parse(tokens)?;
        let end = tokens.consume(Token::Semicolon)?;

        Ok(var_type
            .pos()
            .extend(&id)
            .extend(&equals)
            .extend(&exp)
            .extend(&end)
            .with(VarDecl { var_type: RefCell::new(var_type), id, exp }))
    }
}

impl<'a> Parsable<'a> for FunDecl<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let mut positions = Vec::new();

        let id = Id::parse(tokens)?;
        positions.push(tokens.consume(Token::OpenParen)?);
        let args = Id::parse_many_sep(tokens, Token::Comma)?;
        let close = tokens.consume(Token::CloseParen)?;
        positions.push(close.clone());

        let fun_type = if let Some(Pos { content: Token::HasType, .. }) = tokens.peek() {
            positions.push(tokens.consume(Token::HasType)?);
            let function = Type::parse_function(tokens, &mut Generator::new(), &mut HashMap::new())?;
            function.with(()).with(Some(function))
        } else {
            close.with(None)
        };

        positions.push(tokens.consume(Token::OpenBracket)?);
        let var_decls = VarDecl::parse_many(tokens);
        let stmts = Stmt::parse_many(tokens);
        positions.push(tokens.consume(Token::CloseBracket)?);

        let var_pos = var_decls.join_with(());
        let stmt_pos = stmts.join_with(());

        let fun_decl = FunDecl {
            id,
            args,
            fun_type: RefCell::new(fun_type),
            var_decls,
            stmts,
        };

        let mut result = positions
            .join_with(fun_decl)
            .unwrap();

        if let Some(pos) = var_pos {
            result = result.extend(&pos);
        }

        if let Some(pos) = stmt_pos {
            result = result.extend(&pos);
        }

        Ok(result)
    }
}

/// Parsable for variable type annotations
impl<'a> Parsable<'a> for Option<PType<'a>> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.peek_or_eof("variable type")?;
        match token.content {
            Token::Var => {
                Ok(tokens.consume(Token::Var)?.with(None))
            }
            _ => {
                let parsed = Type::parse_basic(tokens, &mut Generator::new(), &mut HashMap::new())?;
                match parsed.content {
                    Type::Int | Type::Bool | Type::Char | Type::Tuple(_, _) | Type::Array(_) => {
                        let (pos, inner) = parsed.eject();
                        Ok(pos.with(Some(pos.with(inner))))
                    }
                    Type::Polymorphic(_) => Err(parsed.with(ParseError::PolyVar)),
                    _ => Err(parsed.with(ParseError::InvalidAnnotation))
                }
            }
        }
    }
}

/// Parsable for many type class annotations
impl<'a> Parsable<'a> for Vec<Pos<'a, (TypeClass, Id)>> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let type_classes = <(TypeClass, Id)>::parse_many_sep(tokens, Token::Comma)?;
        let arrow = tokens.consume(Token::DoubleArrow)?;
        let pos = type_classes.join_with(()).unwrap_or(arrow.with(()));
        Ok(pos.with(type_classes).extend(&arrow))
    }
}

/// Parsable for type class annotations
impl<'a> Parsable<'a> for (TypeClass, Id) {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let id = Id::parse(tokens)?;
        let class = match id.content.0.as_str() {
            "Any" => TypeClass::Any,
            "Show" => TypeClass::Show,
            "Eq" => TypeClass::Eq,
            "Ord" => TypeClass::Ord,
            _ => return Err(id.with(ParseError::InvalidAnnotation))
        };
        let var = Id::parse(tokens)?;

        Ok(id.extend(&var).with((class, var.content)))
    }
}

impl AsRef<Token> for Token {
    fn as_ref(&self) -> &Token {
        &self
    }
}

impl<'a> Type<'a> {
    /// Parses any type other than a function
    fn parse_basic(tokens: &mut PeekLexer<'a>, gen: &mut Generator, poly_names: &mut HashMap<Id, TypeVariable>) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.next_or_eof("type")?;
        let t = match token.content {
            Token::Void => token.with(Type::Void),
            Token::Int => token.with(Type::Int),
            Token::Bool => token.with(Type::Bool),
            Token::Char => token.with(Type::Char),
            Token::OpenParen => {
                let l = Type::parse_basic(tokens, gen, poly_names)?;
                let comma = tokens.consume(Token::Comma)?;
                let r = Type::parse_basic(tokens, gen, poly_names)?;
                let close = tokens.consume(Token::CloseParen)?;
                token
                    .extend(&l)
                    .extend(&comma)
                    .extend(&r)
                    .extend(&close)
                    .with(Type::Tuple(Box::new(l), Box::new(r)))
            }
            Token::OpenArr => {
                let t = Type::parse_basic(tokens, gen, poly_names)?;
                let close = tokens.consume(Token::CloseArr)?;
                token
                    .extend(&t)
                    .extend(&close)
                    .with(Type::Array(Box::new(t)))
            }
            Token::Identifier(ref s) => {
                let id = Id(s.clone());
                token.with(Type::Polymorphic(poly_names
                    .entry(id).or_insert(gen.fresh())
                    .clone()
                ))
            }
            _ => return Err(token.with(ParseError::BadToken {
                found: token.content.clone(),
                expected: "type".to_owned(),
            }))
        };

        Ok(t)
    }

    /// Parses a function type, including type class constraints
    pub fn parse_function(tokens: &mut PeekLexer<'a>, gen: &mut Generator, poly_names: &mut HashMap<Id, TypeVariable>) -> Result<'a, Pos<'a, Self>> {
        // Read optional type class constraints
        let type_classes = <Vec<Pos<(TypeClass, Id)>>>::try_parse(tokens)
            .unwrap_or(tokens.peek_or_eof("function type")?.with(Vec::new()));
        for p in type_classes.content {
            let (class, var) = p.content;
            poly_names.entry(var).or_insert(gen.fresh()).impose(class);
        }

        let mut arg_types = Vec::new();
        loop {
            let token = tokens.peek_or_eof("type")?;
            match token.content {
                Token::To => break,
                _ => arg_types.push(Type::parse_basic(tokens, gen, poly_names)?)
            }
        }
        let to = tokens.consume(Token::To)?;
        let ret_type = Type::parse_basic(tokens, gen, poly_names)?.extend(&to);
        let fun_type = arg_types
            .into_iter()
            .rfold(ret_type, |res, arg| {
                res
                    .with(())
                    .extend(&arg)
                    .with(Type::Function(Box::new(arg), Box::new(res)))
            });

        Ok(fun_type)
    }
}

impl<'a> Parsable<'a> for Stmt<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.next_or_eof("statement")?;

        let t = match token.content {
            Token::If => {
                let mut positions = vec![token];

                positions.push(tokens.consume(Token::OpenParen)?);
                let condition = Exp::parse(tokens)?;
                positions.push(tokens.consume(Token::CloseParen)?);
                positions.push(tokens.consume(Token::OpenBracket)?);
                let then = Stmt::parse_many(tokens);
                positions.push(tokens.consume(Token::CloseBracket)?);
                let otherwise = if let Some(Pos { content: Token::Else, .. }) = tokens.peek() {
                    positions.push(tokens.consume(Token::Else)?);
                    positions.push(tokens.consume(Token::OpenBracket)?);
                    let result = Stmt::parse_many(tokens);
                    positions.push(tokens.consume(Token::CloseBracket)?);
                    result
                } else {
                    Vec::new()
                };

                let pos = positions
                    .join_with(())
                    .unwrap();

                let t_pos = then.join_with(()).unwrap_or(pos.clone());
                let o_pos = otherwise.join_with(()).unwrap_or(pos.clone());

                pos
                    .extend(&condition)
                    .extend(&t_pos)
                    .extend(&o_pos)
                    .with(Stmt::If(condition, then, otherwise))
            }
            Token::While => {
                let mut positions = vec![token];

                positions.push(tokens.consume(Token::OpenParen)?);
                let condition = Exp::parse(tokens)?;
                positions.push(tokens.consume(Token::CloseParen)?);
                positions.push(tokens.consume(Token::OpenBracket)?);
                let repeat = Stmt::parse_many(tokens);
                positions.push(tokens.consume(Token::CloseBracket)?);

                let pos = positions
                    .join_with(())
                    .unwrap();

                let r_pos = repeat.join_with(()).unwrap_or(pos.clone());

                pos
                    .extend(&condition)
                    .extend(&r_pos)
                    .with(Stmt::While(condition, repeat))
            }
            Token::Return => {
                if let Some(Pos { content: Token::Semicolon, .. }) = tokens.peek() {
                    let end = tokens.consume(Token::Semicolon)?;
                    token
                        .with(Stmt::Return(None))
                        .extend(&end)
                } else {
                    let exp = Exp::parse(tokens)?;
                    let end = tokens.consume(Token::Semicolon)?;
                    token
                        .extend(&exp)
                        .extend(&end)
                        .with(Stmt::Return(Some(exp)))
                }
            }
            Token::Identifier(ref s) => {
                let id = token.with(Id(s.clone()));
                if let Some(Pos { content: Token::OpenParen, .. }) = tokens.peek() {
                    let open = tokens.consume(Token::OpenParen)?;
                    let args = Exp::parse_many_sep(tokens, Token::Comma)?;
                    let close = tokens.consume(Token::CloseParen)?;
                    let end = tokens.consume(Token::Semicolon)?;

                    let pos = args
                        .join_with(())
                        .unwrap_or(open.with(()))
                        .extend(&token)
                        .extend(&open)
                        .extend(&close)
                        .extend(&end);

                    let fun_call = FunCall {
                        id,
                        args,
                        type_args: RefCell::new(Substitution::new()),
                    };

                    pos.with(Stmt::FunCall(fun_call))
                } else {
                    let selector = <Vec<Pos<Field>>>::parse(tokens)?;
                    let equals = tokens.consume(Token::Assign)?;
                    let exp = Exp::parse(tokens)?;
                    let end = tokens.consume(Token::Semicolon)?;

                    token
                        .extend(&selector)
                        .extend(&equals)
                        .extend(&exp)
                        .extend(&end)
                        .with(Stmt::Assignment(id, selector.content, exp))
                }
            }
            _ => return Err(token.pos().with(ParseError::BadToken {
                found: token.content,
                expected: "statement".to_owned(),
            }))
        };

        Ok(t)
    }
}

impl<'a> Exp<'a> {
    fn parse_exp(tokens: &mut PeekLexer<'a>, min_bp: u8) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.next_or_eof("expression")?;

        let mut lhs = match token.content {
            Token::Identifier(ref s) => {
                let id = Id(s.clone());
                if let Some(Pos { content: Token::OpenParen, .. }) = tokens.peek() {
                    let open = tokens.consume(Token::OpenParen)?;
                    let fun_call = FunCall {
                        id: token.with(id),
                        args: Exp::parse_many_sep(tokens, Token::Comma)?,
                        type_args: RefCell::new(Substitution::new()),
                    };
                    let close = tokens.consume(Token::CloseParen)?;
                    let arg_pos = fun_call.args
                        .join_with(())
                        .unwrap_or(token.with(()));
                    token
                        .extend(&open)
                        .extend(&arg_pos)
                        .extend(&close)
                        .with(Exp::FunCall(fun_call))
                } else {
                    let fields = <Vec<Pos<Field>>>::parse(tokens)?;
                    fields.content
                        .into_iter()
                        .fold(token.with(Exp::Variable(id)), |e, f| {
                            let pos = e.pos();
                            let fun_call = FunCall {
                                id: f.with(Id(format!("{}", f.content))),
                                args: vec![e],
                                type_args: RefCell::new(Substitution::new()),
                            };
                            pos.with(Exp::FunCall(fun_call)).extend(&f)
                        })
                }
            }
            Token::Operator(ref op) => {
                let op = token.with(op.clone());
                let r_bp = op.prefix_binding_power()?;
                let rhs = Self::parse_exp(tokens, r_bp)?;
                let pos = rhs.pos();
                let fun_call = FunCall {
                    id: op.prefix_id()?,
                    args: vec![rhs],
                    type_args: RefCell::new(Substitution::new()),
                };
                token
                    .extend(&pos)
                    .with(Exp::FunCall(fun_call))
            }
            Token::Number(n) => token.with(Exp::Number(n)),
            Token::Character(c) => token.with(Exp::Character(c)),
            Token::False => token.with(Exp::Boolean(false)),
            Token::True => token.with(Exp::Boolean(true)),
            Token::OpenParen => {
                let lhs = Self::parse_exp(tokens, 0)?;
                if let Some(Pos { content: Token::CloseParen, .. }) = tokens.peek() {
                    let close = tokens.consume(Token::CloseParen)?;
                    lhs
                        .extend(&token)
                        .extend(&close)
                } else {
                    let comma = tokens.consume(Token::Comma)?;
                    let rhs = Self::parse_exp(tokens, 0)?;
                    let close = tokens.consume(Token::CloseParen)?;
                    token
                        .extend(&lhs)
                        .extend(&comma)
                        .extend(&rhs)
                        .extend(&close)
                        .with(Exp::Tuple(Box::new(lhs), Box::new(rhs)))
                }
            }
            Token::Nil => token.with(Exp::Nil),
            _ => return Err(token.pos().with(ParseError::BadToken {
                found: token.content,
                expected: "expression".to_owned(),
            }))
        };

        while let Some(Pos { content: Token::Operator(op), .. }) = tokens.peek() {
            let op = op.clone();
            let op = tokens.peek().unwrap().with(op);
            let (l_bp, r_bp) = op.infix_binding_power()?;

            if l_bp < min_bp {
                break;
            }

            tokens.next();
            let rhs = Self::parse_exp(tokens, r_bp)?;

            let pos = lhs
                .pos()
                .extend(&op)
                .extend(&rhs);

            let fun_call = FunCall {
                id: op.infix_id()?,
                args: vec![lhs, rhs],
                type_args: RefCell::new(Substitution::new()),
            };

            lhs = pos.with(Exp::FunCall(fun_call));
        }

        Ok(lhs)
    }
}

impl<'a> Pos<'a, Operator> {
    fn prefix_binding_power(&self) -> Result<'a, u8> {
        let bp = match self.content {
            Operator::Minus => 17,
            Operator::Not => 7,
            _ => return Err(self.with(ParseError::Fixity {
                found: self.content.clone(),
                prefix: true,
            }))
        };

        Ok(bp)
    }

    fn infix_binding_power(&self) -> Result<'a, (u8, u8)> {
        let bp = match self.content {
            Operator::Times | Operator::Divide | Operator::Modulo => (15, 16),
            Operator::Plus | Operator::Minus => (13, 14),
            Operator::Smaller | Operator::Greater |
            Operator::SmallerEqual | Operator::GreaterEqual => (11, 12),
            Operator::Equals | Operator::NotEqual => (9, 10),
            Operator::And => (6, 5),
            Operator::Or => (4, 3),
            Operator::Cons => (2, 1),
            _ => return Err(self.with(ParseError::Fixity {
                found: self.content.clone(),
                prefix: false,
            }))
        };

        Ok(bp)
    }

    pub fn prefix_id(&self) -> Result<'a, Pos<'a, Id>> {
        let name = match self.content {
            Operator::Not => "not",
            Operator::Minus => "neg",
            _ => return Err(self.with(ParseError::Fixity {
                found: self.content.clone(),
                prefix: true,
            }))
        };

        Ok(self.with(Id(name.to_owned())))
    }

    pub fn infix_id(&self) -> Result<'a, Pos<'a, Id>> {
        let name = match self.content {
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
            _ => return Err(self.with(ParseError::Fixity {
                found: self.content.clone(),
                prefix: false,
            }))
        };

        Ok(self.with(Id(name.to_owned())))
    }
}

impl<'a> Parsable<'a> for Exp<'a> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        Self::parse_exp(tokens, 0)
    }
}

impl<'a> Parsable<'a> for Vec<Pos<'a, Field>> {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let mut fields = Vec::new();

        let pos = tokens.peek_or_eof("fields")?.with(());

        while let Some(Pos { content: Token::Field(_), .. }) = tokens.peek() {
            let token = tokens.next().unwrap();
            let pos = token.pos();
            if let Token::Field(field) = token.content {
                fields.push(pos.with(field));
            }
        }

        Ok(fields.join_with(()).unwrap_or(pos).with(fields))
    }
}

impl<'a> Parsable<'a> for Id {
    fn parse(tokens: &mut PeekLexer<'a>) -> Result<'a, Pos<'a, Self>> {
        let token = tokens.next_or_eof("identifier")?;
        match token.content {
            Token::Identifier(ref s) => Ok(token.with(Id(s.clone()))),
            _ => Err(token.pos().with(ParseError::BadToken {
                found: token.content,
                expected: "identifier".to_owned(),
            }))
        }
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::lexer::{Operator, Token};
    use crate::position::Pos;

    pub type Result<'a, T, E = Pos<'a, ParseError>> = std::result::Result<T, E>;

    #[derive(Clone, Debug)]
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

    impl fmt::Display for ParseError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                ParseError::BadToken { found, expected } =>
                    write!(f, "Bad token {:?}, expected: {}", found, expected),
                ParseError::EOF { expected } =>
                    write!(f, "Unexpected end of file, expected {}", expected),
                ParseError::Fixity { found, prefix } =>
                    write!(f, "{:?} is not a{}fix operator", found, if *prefix { " pre" } else { "n in" }),
                ParseError::InvalidAnnotation =>
                    write!(f, "Variables cannot have a function or void type"),
                ParseError::PolyVar =>
                    write!(f, "Use the 'var' keyword to indicate a polymorphic variable")
            }
        }
    }

    impl Error for Pos<'_, ParseError> {}
}
