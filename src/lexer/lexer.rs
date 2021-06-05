use std::fmt;
use std::fmt::{Debug, Display};
use std::iter::Peekable;
use std::ops::{Deref, DerefMut};

use error::Result;

use crate::lexer::{CharIterable, CharIterator};
use crate::lexer::error::LexError;
use crate::position::Pos;

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Var,
    Assign,
    Semicolon,
    OpenParen,
    CloseParen,
    HasType,
    OpenBracket,
    CloseBracket,
    Void,
    DoubleArrow,
    To,
    Comma,
    OpenArr,
    CloseArr,

    Int,
    Bool,
    Char,

    If,
    Else,
    While,
    Return,

    False,
    True,
    Nil,

    Field(Field),

    Operator(Operator),

    Number(i32),
    Character(char),
    Identifier(String),
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Token::Var => write!(f, "var"),
            Token::Assign => write!(f, "="),
            Token::Semicolon => write!(f, ";"),
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::HasType => write!(f, "::"),
            Token::OpenBracket => write!(f, "{{"),
            Token::CloseBracket => write!(f, "}}"),
            Token::Void => write!(f, "Void"),
            Token::DoubleArrow => write!(f, "=>"),
            Token::To => write!(f, "->"),
            Token::Comma => write!(f, ","),
            Token::OpenArr => write!(f, "["),
            Token::CloseArr => write!(f, "]"),
            Token::Int => write!(f, "Int"),
            Token::Bool => write!(f, "Bool"),
            Token::Char => write!(f, "Char"),
            Token::If => write!(f, "if"),
            Token::Else => write!(f, "else"),
            Token::While => write!(f, "while"),
            Token::Return => write!(f, "return"),
            Token::False => write!(f, "False"),
            Token::True => write!(f, "True"),
            Token::Nil => write!(f, "[]"),
            Token::Field(field) => write!(f, ".{}", field),
            Token::Operator(op) => write!(f, "{}", op),
            Token::Number(n) => write!(f, "{}", n),
            Token::Character(c) => write!(f, "{}", c),
            Token::Identifier(id) => write!(f, "{}", id)
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operator {
    Not,

    Plus,
    Minus,
    Times,
    Divide,
    Modulo,
    Equals,
    Smaller,
    Greater,
    SmallerEqual,
    GreaterEqual,
    NotEqual,
    And,
    Or,
    Cons,
}

impl fmt::Display for Operator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Operator::Not => write!(f, "!"),
            Operator::Plus => write!(f, "+"),
            Operator::Minus => write!(f, "-"),
            Operator::Times => write!(f, "*"),
            Operator::Divide => write!(f, "/"),
            Operator::Modulo => write!(f, "%"),
            Operator::Equals => write!(f, "=="),
            Operator::Smaller => write!(f, "<"),
            Operator::Greater => write!(f, ">"),
            Operator::SmallerEqual => write!(f, "<="),
            Operator::GreaterEqual => write!(f, ">="),
            Operator::NotEqual => write!(f, "!="),
            Operator::And => write!(f, "&&"),
            Operator::Or => write!(f, "||"),
            Operator::Cons => write!(f, ":")
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Field {
    Head,
    Tail,
    First,
    Second,
}

impl fmt::Display for Field {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Field::Head => write!(f, "hd"),
            Field::Tail => write!(f, "tl"),
            Field::First => write!(f, "fst"),
            Field::Second => write!(f, "snd"),
        }
    }
}

pub trait Lexable<'a> {
    fn tokenize(self) -> Result<'a, Lexer<'a>>;
}

impl<'a> Lexable<'a> for &'a str {
    fn tokenize(self) -> Result<'a, Lexer<'a>> {
        // Create lexer
        let mut lexer = Lexer {
            code: self,
            chars: self.iter_char().peekable(),
            errors: Vec::new(),
        };
        // Consume lexer to look for errors
        lexer.by_ref().for_each(drop);
        if lexer.errors.is_empty() {
            // No errors, return identical lexer
            Ok(Lexer {
                code: self,
                chars: self.iter_char().peekable(),
                errors: Vec::new(),
            })
        } else {
            // Errors found
            return Err(lexer.errors);
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lexer<'a> {
    code: &'a str,
    chars: Peekable<CharIterator<'a>>,
    errors: Vec<Pos<'a, LexError>>,
}

#[derive(Clone, Debug)]
pub struct PeekLexer<'a> {
    pub code: &'a str,
    lexer: Peekable<Lexer<'a>>,
}

impl<'a> Deref for PeekLexer<'a> {
    type Target = Peekable<Lexer<'a>>;

    fn deref(&self) -> &Self::Target {
        &self.lexer
    }
}

impl<'a> DerefMut for PeekLexer<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lexer
    }
}

impl<'a> Lexer<'a> {
    pub fn peekable(self) -> PeekLexer<'a> {
        PeekLexer {
            code: self.code,
            lexer: <Self as Iterator>::peekable(self),
        }
    }

    fn followed_by(&mut self, c: char) -> bool {
        match self.chars.peek() {
            None => false,
            Some(d) => if c == d.content {
                self.chars.next();
                true
            } else {
                false
            }
        }
    }

    fn read_number(&mut self, start: char) -> i32 {
        let mut digits: Vec<char> = vec![start];

        while let Some(c) = self.chars.peek() {
            if c.is_ascii_digit() {
                digits.push(*self.chars.next().unwrap())
            } else {
                break;
            }
        }

        digits.into_iter().collect::<String>().parse::<i32>().unwrap()
    }

    fn read_word(&mut self, start: char) -> String {
        let mut chars = vec![start];

        while let Some(c) = self.chars.peek() {
            if c.is_alphanumeric() || **c == '_' {
                chars.push(*self.chars.next().unwrap())
            } else {
                break;
            }
        }

        chars.into_iter().collect()
    }

    fn expected(&mut self, expected: impl Display) {
        self.errors.push(if let Some(c) = self.chars.peek() {
            c.with(LexError::Unexpected {
                found: c.content,
                expected: expected.to_string(),
            })
        } else {
            let row = self.code.lines().count();
            let col = self.code.lines().last().unwrap_or("").len() + 1;
            Pos::new(row, col, self.code, LexError::EOF { expected: expected.to_string() })
        });
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Pos<'a, Token>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.chars.next()?;

        let token = match *current {
            '=' => if self.followed_by('=') {
                current.with(Token::Operator(Operator::Equals)).grow(1)
            } else if self.followed_by('>') {
                current.with(Token::DoubleArrow).grow(1)
            } else {
                current.with(Token::Assign)
            }
            '<' => if self.followed_by('=') {
                current.with(Token::Operator(Operator::SmallerEqual)).grow(1)
            } else {
                current.with(Token::Operator(Operator::Smaller))
            }
            '>' => if self.followed_by('=') {
                current.with(Token::Operator(Operator::GreaterEqual)).grow(1)
            } else {
                current.with(Token::Operator(Operator::Greater))
            }
            '!' => if self.followed_by('=') {
                current.with(Token::Operator(Operator::NotEqual)).grow(1)
            } else {
                current.with(Token::Operator(Operator::Not))
            }
            '&' => if self.followed_by('&') {
                current.with(Token::Operator(Operator::And)).grow(1)
            } else {
                self.expected('&');
                current.with(Token::Operator(Operator::And))
            }
            '|' => if self.followed_by('|') {
                current.with(Token::Operator(Operator::Or)).grow(1)
            } else {
                self.expected('|');
                current.with(Token::Operator(Operator::Or))
            }
            ':' => if self.followed_by(':') {
                current.with(Token::HasType).grow(1)
            } else {
                current.with(Token::Operator(Operator::Cons))
            }
            '[' => if self.followed_by(']') {
                current.with(Token::Nil).grow(1)
            } else {
                current.with(Token::OpenArr)
            }
            '-' => if self.followed_by('>') {
                current.with(Token::To).grow(1)
            } else {
                current.with(Token::Operator(Operator::Minus))
            }
            '+' => current.with(Token::Operator(Operator::Plus)),
            '*' => current.with(Token::Operator(Operator::Times)),
            '%' => current.with(Token::Operator(Operator::Modulo)),
            ']' => current.with(Token::CloseArr),
            ';' => current.with(Token::Semicolon),
            '(' => current.with(Token::OpenParen),
            ')' => current.with(Token::CloseParen),
            '{' => current.with(Token::OpenBracket),
            '}' => current.with(Token::CloseBracket),
            ',' => current.with(Token::Comma),
            '/' => if self.followed_by('/') {
                while let Some(c) = self.chars.next() {
                    if *c == '\n' {
                        break;
                    }
                }
                return self.next();
            } else if self.followed_by('*') {
                let mut depth = 1;
                loop {
                    while let Some(c) = self.chars.next() {
                        if *c == '*' && self.followed_by('/') {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        } else if *c == '/' && self.followed_by('*') {
                            depth += 1;
                        }
                    }
                    return self.next();
                }
            } else {
                current.with(Token::Operator(Operator::Divide))
            },
            '\'' => match self.chars.next() {
                Some(c) => if self.followed_by('\'') {
                    current.with(Token::Character(*c)).grow(2)
                } else {
                    self.expected('\'');
                    current.with(Token::Character(*c)).grow(1)
                }
                None => {
                    self.expected("character");
                    current.with(Token::Character('c'))
                }
            }
            'a'..='z' | 'A'..='Z' => match self.read_word(*current).as_str() {
                "Int" => current.with(Token::Int).grow(2),
                "Bool" => current.with(Token::Bool).grow(3),
                "Char" => current.with(Token::Char).grow(3),
                "Void" => current.with(Token::Void).grow(3),
                "if" => current.with(Token::If).grow(1),
                "else" => current.with(Token::Else).grow(3),
                "while" => current.with(Token::While).grow(4),
                "return" => current.with(Token::Return).grow(5),
                "True" => current.with(Token::True).grow(3),
                "False" => current.with(Token::False).grow(4),
                "var" => current.with(Token::Var).grow(2),
                id => current.with(Token::Identifier(id.to_owned())).grow(id.len() - 1)
            }
            '.' => match self.read_word(*current).as_str() {
                ".hd" => current.with(Token::Field(Field::Head)).grow(2),
                ".tl" => current.with(Token::Field(Field::Tail)).grow(2),
                ".fst" => current.with(Token::Field(Field::First)).grow(3),
                ".snd" => current.with(Token::Field(Field::Second)).grow(3),
                f => {
                    self.errors.push(current.with(LexError::Field { found: f.to_owned() }));
                    return self.next();
                }
            }
            '0'..='9' => {
                let number = self.read_number(*current);
                current.with(Token::Number(number)).grow(number.to_string().len() - 1)
            }
            ' ' | '\r' | '\n' | '\t' => return self.next(),
            _ => {
                self.errors.push(current.with(LexError::Invalid { found: *current }));
                return self.next();
            }
        };

        Some(token)
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    use crate::position::Pos;

    pub type Result<'a, T, E = Vec<Pos<'a, LexError>>> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum LexError {
        Unexpected { found: char, expected: String },
        EOF { expected: String },
        Invalid { found: char },
        Field { found: String },
    }

    impl fmt::Display for LexError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                LexError::Unexpected { found, expected } =>
                    write!(f, "Unexpected character '{}', expected: {}", found, expected),
                LexError::EOF { expected } =>
                    write!(f, "Unexpected EOF\nExpected: {}", expected),
                LexError::Invalid { found } =>
                    write!(f, "Invalid character '{}'", found),
                LexError::Field { found } =>
                    write!(f, "Unexpected field '{}', expected: .hd, .tl, .fst, .snd", found)
            }
        }
    }

    impl Debug for LexError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for LexError {}
}
