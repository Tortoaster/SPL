use std::str::Chars;
use std::iter::Peekable;

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Field {
    Head, // hd
    Tail, // tl
    First, // fst
    Second, // snd
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

#[derive(Clone)]
pub struct Lexer<'a> {
    code: &'a str,
    chars: Peekable<Chars<'a>>,
}

impl<'a> Lexer<'a> {
    pub fn new(code: &'a str) -> Self {
        let code = code;
        Lexer {
            code,
            chars: code.chars().peekable(),
        }
    }

    fn followed_by(&mut self, c: char) -> bool {
        match self.chars.peek() {
            None => false,
            Some(d) => if c == *d {
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
                digits.push(self.chars.next().unwrap())
            } else {
                break;
            }
        }

        digits.into_iter().collect::<String>().parse::<i32>().unwrap()
    }

    fn read_word(&mut self, start: char) -> String {
        let mut chars = vec![start];

        while let Some(c) = self.chars.peek() {
            if c.is_alphanumeric() || *c == '_' {
                chars.push(self.chars.next().unwrap())
            } else {
                break;
            }
        }

        chars.into_iter().collect()
    }

    fn abort(&mut self) -> Token {
        panic!("Unexpected character '{:?}' at {}:{}:\n{}", self.chars.peek(), 0, 0, self.code)
    }
}

impl Iterator for Lexer<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let current = self.chars.next()?;

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
                    self.abort()
                }
                '|' => if self.followed_by('|') {
                    Token::Operator(Operator::Or)
                } else {
                    self.abort()
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
                    while let Some(c) = self.chars.next() {
                        if c == '\n' {
                            break;
                        }
                    }
                    return self.next();
                } else if self.followed_by('*') {
                    loop {
                        while let Some(c) = self.chars.next() {
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
                    if let Some(c) = self.chars.next() {
                        if let Some('\'') = self.chars.peek() {
                            self.chars.next();
                            Token::Character(c)
                        } else {
                            self.abort()
                        }
                    } else {
                        self.abort()
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
                _ => panic!("Invalid character '{:?}' at {}:{}:\n{}", current, 0, 0, self.code)
            }
        )
    }
}
