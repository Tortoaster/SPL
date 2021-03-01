use std::error::Error;
use std::fmt;
use std::fmt::Display;
use std::iter::Peekable;

use crate::char_iterator::{CharIterable, CharIterator};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Operator {
    Not, // !

    Plus, // +
    Minus, // -
    Times, // *
    Divide, // /
    Modulo, // %
    Equals, // ==
    Smaller, // <
    Greater, // >
    SmallerEqual, // <=
    GreaterEqual, // >=
    NotEqual, // !=
    And, // &&
    Or, // ||
    Cons, // :
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
    Head, // hd
    Tail, // tl
    First, // fst
    Second, // snd
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Token {
    Var, // var
    Assign, // =
    Semicolon, // ;
    OpenParen, // (
    CloseParen, // )
    HasType, // ::
    OpenBracket, // {
    CloseBracket, // }
    Void, // Void
    To, // ->
    Comma, // ,
    OpenArr, // [
    CloseArr, // ]

    Int, // Int
    Bool, // Bool
    Char, // Char

    If, // if
    Else, // else
    While, // while
    Return, // return

    False, // False,
    True, // True,
    Nil, // []

    Dot, // .
    Field(Field),

    Operator(Operator),

    Number(i32),
    Character(char),
    Identifier(String),
}

#[derive(Clone, Debug)]
pub enum LexError<'a> {
    Unexpected {
        found: char,
        row: usize,
        col: usize,
        code: &'a str,
        expected: String,
    },
    EOF { expected: String },
    Invalid {
        found: char,
        row: usize,
        col: usize,
        code: &'a str,
    }
}

impl fmt::Display for LexError<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LexError::Unexpected { found, row, col, code, expected} => write!(
                f,
                "Unexpected character '{}' at {}:{}:\n{}\n{: >indent$}\nExpected: {}",
                found,
                row,
                col,
                code.lines().nth(*row).unwrap(),
                "^",
                expected,
                indent = col + 1
            ),
            LexError::EOF { expected } => write!(f, "Unexpected EOF\nExpected: {}", expected),
            LexError::Invalid { found, row, col, code } => write!(
                f,
                "Invalid character '{}' at {}:{}:\n{}\n{: >indent$}",
                found,
                row,
                col,
                code.lines().nth(*row).unwrap(),
                "^",
                indent = col + 1
            )
        }
    }
}

impl Error for LexError<'_> {}

pub trait Lexable<'a> {
    fn tokenize(self) -> Lexer<'a>;
}

impl<'a> Lexable<'a> for &'a str {
    fn tokenize(self) -> Lexer<'a> {
        Lexer {
            code: self,
            chars: self.iter_char().peekable(),
            errors: Vec::new()
        }
    }
}

#[derive(Clone, Debug)]
pub struct Lexer<'a> {
    code: &'a str,
    chars: Peekable<CharIterator<'a>>,
    pub errors: Vec<LexError<'a>>
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
        if let Some(((row, col), c)) = self.chars.peek() {
            self.errors.push(LexError::Unexpected {
                found: *c,
                row: *row,
                col: *col,
                code: self.code,
                expected: expected.to_string()
            })
        } else {
            self.errors.push(LexError::EOF {
                expected: expected.to_string()
            })
        }
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let ((row, col), current) = self.chars.next()?;

        Some(
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
                '.' => Token::Dot,
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
                '\'' => {
                    match self.chars.next() {
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
                }
                'a'..='z' | 'A'..='Z' => {
                    match self.read_word(current).as_str() {
                        "Int" => Token::Int,
                        "Bool" => Token::Bool,
                        "Char" => Token::Char,
                        "Void" => Token::Void,
                        "hd" => Token::Field(Field::Head),
                        "tl" => Token::Field(Field::Tail),
                        "fst" => Token::Field(Field::First),
                        "snd" => Token::Field(Field::Second),
                        "if" => Token::If,
                        "else" => Token::Else,
                        "while" => Token::While,
                        "return" => Token::Return,
                        "True" => Token::True,
                        "False" => Token::False,
                        "var" => Token::Var,
                        id => Token::Identifier(String::from(id))
                    }
                },
                '0'..='9' => Token::Number(self.read_number(current)),
                ' ' | '\r' | '\n' | '\t' => return self.next(),
                _ => {
                    self.errors.push(LexError::Invalid {
                        found: current,
                        row,
                        col,
                        code: self.code,
                    });
                    return None;
                }
            }
        )
    }
}
