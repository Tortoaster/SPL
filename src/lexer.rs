use std::fmt;
use std::fmt::{Debug, Display};
use std::iter::Peekable;

use error::Result;

use crate::char_iterator::{CharIterable, CharIterator};
use crate::lexer::error::LexError;

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
            Operator::Cons => write!(f, ":"),
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
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
    fn tokenize(self) -> Result<Lexer<'a>>;
}

impl<'a> Lexable<'a> for &'a str {
    fn tokenize(self) -> Result<Lexer<'a>> {
        let mut lexer = Lexer {
            code: self,
            chars: self.iter_char().peekable(),
            errors: Vec::new(),
        };
        while let Some(_) = lexer.next() {}
        if lexer.errors.is_empty() {
            Ok(Lexer {
                code: self,
                chars: self.iter_char().peekable(),
                errors: Vec::new(),
            })
        } else {
            return Err(lexer.errors);
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lexer<'a> {
    code: &'a str,
    chars: Peekable<CharIterator<'a>>,
    errors: Vec<LexError>,
}

impl<'a> Lexer<'a> {
    fn followed_by(&mut self, c: char) -> bool {
        match self.chars.peek() {
            None => false,
            Some((_, d)) => if c == *d {
                self.chars.next();
                true
            } else {
                false
            }
        }
    }

    fn read_number(&mut self, start: char) -> i32 {
        let mut digits: Vec<char> = vec![start];

        while let Some((_, c)) = self.chars.peek() {
            if c.is_ascii_digit() {
                digits.push(self.chars.next().unwrap().1)
            } else {
                break;
            }
        }

        digits.into_iter().collect::<String>().parse::<i32>().unwrap()
    }

    fn read_word(&mut self, start: char) -> String {
        let mut chars = vec![start];

        while let Some((_, c)) = self.chars.peek() {
            if c.is_alphanumeric() || *c == '_' {
                chars.push(self.chars.next().unwrap().1)
            } else {
                break;
            }
        }

        chars.into_iter().collect()
    }

    fn expected(&mut self, expected: impl Display) {
        self.errors.push(if let Some(((row, col), c)) = self.chars.peek() {
            LexError::Unexpected {
                found: *c,
                row: *row,
                col: *col,
                code: self.code.to_owned(),
                expected: expected.to_string(),
            }
        } else {
            LexError::EOF {
                expected: expected.to_string()
            }
        });
    }
}

impl Iterator for Lexer<'_> {
    type Item = ((usize, usize), Token);

    fn next(&mut self) -> Option<Self::Item> {
        let ((row, col), current) = self.chars.next()?;

        Some(((row, col),
            match current {
                '=' => if self.followed_by('=') {
                    Token::Operator(Operator::Equals)
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
                    while let Some((_, c)) = self.chars.next() {
                        if c == '\n' {
                            break;
                        }
                    }
                    return self.next();
                } else if self.followed_by('*') {
                    loop {
                        while let Some((_, c)) = self.chars.next() {
                            if c == '*' {
                                break;
                            }
                        }
                        if self.followed_by('/') {
                            return self.next();
                        }
                    }
                } else {
                    Token::Operator(Operator::Divide)
                },
                '\'' => match self.chars.next() {
                    Some((_, c)) => if self.followed_by('\'') {
                        Token::Character(c)
                    } else {
                        self.expected('\'');
                        Token::Character(c)
                    }
                    None => {
                        self.expected("character");
                        Token::Character('c')
                    }
                }
                'a'..='z' | 'A'..='Z' => match self.read_word(current).as_str() {
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
                    id => Token::Identifier(String::from(id))
                }
                '.' => match self.read_word(current).as_str() {
                    ".hd" => Token::Field(Field::Head),
                    ".tl" => Token::Field(Field::Tail),
                    ".fst" => Token::Field(Field::First),
                    ".snd" => Token::Field(Field::Second),
                    f => {
                        self.errors.push(LexError::Field {
                            found: f.to_owned(),
                            row,
                            col,
                            code: self.code.to_owned(),
                        });
                        return self.next();
                    }
                }
                '0'..='9' => Token::Number(self.read_number(current)),
                ' ' | '\r' | '\n' | '\t' => return self.next(),
                _ => {
                    self.errors.push(LexError::Invalid {
                        found: current,
                        row,
                        col,
                        code: self.code.to_owned(),
                    });
                    return self.next();
                }
            }
        ))
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    pub type Result<T, E = Vec<LexError>> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum LexError {
        Unexpected {
            found: char,
            row: usize,
            col: usize,
            code: String,
            expected: String,
        },
        EOF { expected: String },
        Invalid {
            found: char,
            row: usize,
            col: usize,
            code: String,
        },
        Field {
            found: String,
            row: usize,
            col: usize,
            code: String,
        }
    }

    impl fmt::Display for LexError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                LexError::Unexpected { found, row, col, code, expected } => write!(
                    f,
                    "Unexpected character '{}' at {}:{}:\n{}\n{: >indent$}\nExpected: {}",
                    found,
                    row,
                    col,
                    code.lines().nth(*row - 1).unwrap(),
                    "^",
                    expected,
                    indent = col - 1
                ),
                LexError::EOF { expected } => write!(f, "Unexpected EOF\nExpected: {}", expected),
                LexError::Invalid { found, row, col, code } => write!(
                    f,
                    "Invalid character '{}' at {}:{}:\n{}\n{: >indent$}",
                    found,
                    row,
                    col,
                    code.lines().nth(*row - 1).unwrap(),
                    "^",
                    indent = col - 1
                ),
                LexError::Field { found, row, col, code } => write!(
                    f,
                    "Unexpected field '{}' at {}:{}:\n{}\n{: >indent$}\nExpected: .hd, .tl, .fst, .snd",
                    found,
                    row,
                    col,
                    code.lines().nth(*row - 1).unwrap(),
                    "^",
                    indent = col - 1
                )
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
