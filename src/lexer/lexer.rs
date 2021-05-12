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
            Some(d) => if c == d.inner {
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
                found: c.inner,
                expected: expected.to_string(),
            })
        } else {
            Pos {
                row: self.code.lines().count(),
                col: self.code.lines().last().unwrap_or("").len() + 1,
                code: self.code,
                inner: LexError::EOF {
                    expected: expected.to_string()
                },
            }
        });
    }
}

impl<'a> Iterator for Lexer<'a> {
    type Item = Pos<'a, Token>;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.chars.next()?;

        let token = match *current {
            '=' => if self.followed_by('=') {
                Token::Operator(Operator::Equals)
            } else if self.followed_by('>') {
                Token::DoubleArrow
            } else {
                Token::Assign
            }
            '<' => if self.followed_by('=') {
                Token::Operator(Operator::SmallerEqual)
            } else {
                Token::Operator(Operator::Smaller)
            }
            '>' => if self.followed_by('=') {
                Token::Operator(Operator::GreaterEqual)
            } else {
                Token::Operator(Operator::Greater)
            }
            '!' => if self.followed_by('=') {
                Token::Operator(Operator::NotEqual)
            } else {
                Token::Operator(Operator::Not)
            }
            '&' => if self.followed_by('&') {
                Token::Operator(Operator::And)
            } else {
                self.expected('&');
                Token::Operator(Operator::And)
            }
            '|' => if self.followed_by('|') {
                Token::Operator(Operator::Or)
            } else {
                self.expected('|');
                Token::Operator(Operator::Or)
            }
            ':' => if self.followed_by(':') {
                Token::HasType
            } else {
                Token::Operator(Operator::Cons)
            }
            '[' => if self.followed_by(']') {
                Token::Nil
            } else {
                Token::OpenArr
            }
            '-' => if self.followed_by('>') {
                Token::To
            } else {
                Token::Operator(Operator::Minus)
            }
            '+' => Token::Operator(Operator::Plus),
            '*' => Token::Operator(Operator::Times),
            '%' => Token::Operator(Operator::Modulo),
            ']' => Token::CloseArr,
            ';' => Token::Semicolon,
            '(' => Token::OpenParen,
            ')' => Token::CloseParen,
            '{' => Token::OpenBracket,
            '}' => Token::CloseBracket,
            ',' => Token::Comma,
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
                Token::Operator(Operator::Divide)
            },
            '\'' => match self.chars.next() {
                Some(c) => if self.followed_by('\'') {
                    Token::Character(*c)
                } else {
                    self.expected('\'');
                    Token::Character(*c)
                }
                None => {
                    self.expected("character");
                    Token::Character('c')
                }
            }
            'a'..='z' | 'A'..='Z' => match self.read_word(*current).as_str() {
                "Int" => Token::Int,
                "Bool" => Token::Bool,
                "Char" => Token::Char,
                "Void" => Token::Void,
                "if" => Token::If,
                "else" => Token::Else,
                "while" => Token::While,
                "return" => Token::Return,
                "True" => Token::True,
                "False" => Token::False,
                "var" => Token::Var,
                id => Token::Identifier(id.to_owned())
            }
            '.' => match self.read_word(*current).as_str() {
                ".hd" => Token::Field(Field::Head),
                ".tl" => Token::Field(Field::Tail),
                ".fst" => Token::Field(Field::First),
                ".snd" => Token::Field(Field::Second),
                f => {
                    self.errors.push(current.with(LexError::Field { found: f.to_owned() }));
                    return self.next();
                }
            }
            '0'..='9' => Token::Number(self.read_number(*current)),
            ' ' | '\r' | '\n' | '\t' => return self.next(),
            _ => {
                self.errors.push(current.with(LexError::Invalid { found: *current }));
                return self.next();
            }
        };

        Some(current.with(token))
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
