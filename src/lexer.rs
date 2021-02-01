use std::str::Chars;
use std::iter::Peekable;

#[derive(Debug, Eq, PartialEq)]
pub enum BasicType {
    Int, // Int
    Bool, // Bool
    Char, // Char
}

#[derive(Debug, Eq, PartialEq)]
pub enum Stmt {
    If, // if
    Else, // else
    While, // while
    Return, // return
}

#[derive(Debug, Eq, PartialEq)]
pub enum Expr {
    False, // False,
    True, // True,
    Nil, // []
}

#[derive(Debug, Eq, PartialEq)]
pub enum Field {
    Dot, // .
    Head, // hd
    Tail, // tl
    First, // fst
    Second, // snd
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PrefixOp {
    Not, // !
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum InfixOp {
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

#[derive(Debug, Eq, PartialEq)]
pub enum Token {
    Var, // var
    Assign, // =
    Terminal, // ;
    OpenParen, // (
    CloseParen, // )
    HasType, // ::
    OpenBrac, // {
    CloseBrac, // }
    Void, // Void
    To, // ->
    Separator, // ,
    OpenArr, // [
    CloseArr, // ]
    Basic(BasicType),
    Statement(Stmt),
    Expression(Expr),
    Field(Field),
    Op1(PrefixOp),
    Op2(InfixOp),
    Number(i32),
    Character(char),
    Id(String),
}

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

    fn read_number(&mut self, start: Option<char>) -> i32 {
        let mut digits: Vec<char> = start.into_iter().collect();

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
                    Token::Op2(InfixOp::Equals)
                } else {
                    Token::Assign
                }
                '<' => if self.followed_by('=') {
                    Token::Op2(InfixOp::SmallerEqual)
                } else {
                    Token::Op2(InfixOp::Smaller)
                }
                '>' => if self.followed_by('=') {
                    Token::Op2(InfixOp::GreaterEqual)
                } else {
                    Token::Op2(InfixOp::Greater)
                }
                '!' => if self.followed_by('=') {
                    Token::Op2(InfixOp::NotEqual)
                } else {
                    Token::Op1(PrefixOp::Not)
                }
                '&' => if self.followed_by('&') {
                    Token::Op2(InfixOp::And)
                } else {
                    self.abort()
                }
                '|' => if self.followed_by('|') {
                    Token::Op2(InfixOp::Or)
                } else {
                    self.abort()
                }
                ':' => if self.followed_by(':') {
                    Token::HasType
                } else {
                    Token::Op2(InfixOp::Cons)
                }
                '[' => if self.followed_by(']') {
                    Token::Expression(Expr::Nil)
                } else {
                    Token::OpenArr
                }
                '+' => Token::Op2(InfixOp::Plus),
                '*' => Token::Op2(InfixOp::Times),
                '%' => Token::Op2(InfixOp::Modulo),
                ']' => Token::CloseArr,
                '.' => Token::Field(Field::Dot),
                ';' => Token::Terminal,
                '(' => Token::OpenParen,
                ')' => Token::CloseParen,
                '{' => Token::OpenBrac,
                '}' => Token::CloseBrac,
                ',' => Token::Separator,
                '-' => if self.followed_by('>') {
                    Token::To
                } else if let Some(c) = self.chars.peek() {
                    if c.is_ascii_digit() {
                        Token::Number(-self.read_number(None))
                    } else {
                        Token::Op2(InfixOp::Minus)
                    }
                } else {
                    self.abort()
                }
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
                    Token::Op2(InfixOp::Divide)
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
                        "Int" => Token::Basic(BasicType::Int),
                        "Bool" => Token::Basic(BasicType::Bool),
                        "Char" => Token::Basic(BasicType::Char),
                        "Void" => Token::Void,
                        "hd" => Token::Field(Field::Head),
                        "tl" => Token::Field(Field::Tail),
                        "fst" => Token::Field(Field::First),
                        "snd" => Token::Field(Field::Second),
                        "if" => Token::Statement(Stmt::If),
                        "else" => Token::Statement(Stmt::Else),
                        "while" => Token::Statement(Stmt::While),
                        "return" => Token::Statement(Stmt::Return),
                        "True" => Token::Expression(Expr::True),
                        "False" => Token::Expression(Expr::False),
                        "var" => Token::Var,
                        id => Token::Id(String::from(id))
                    }
                },
                '0'..='9' => Token::Number(self.read_number(Some(current))),
                ' ' | '\r' | '\n' | '\t' => return self.next(),
                _ => panic!("Invalid character '{:?}' at {}:{}:\n{}", current, 0, 0, self.code)
            }
        )
    }
}

#[cfg(test)]
mod tests {
    use std::fs;
    use crate::lexer::{Token, Lexer, BasicType, Stmt, InfixOp};

    #[test]
    fn lex_fac() {
        let code = fs::read_to_string("tests/fac.spl").expect("File inaccessible");
        let tokens: Vec<Token> = Lexer::new(&code[..]).collect();
        let expected = vec![
            Token::Id("fac".into()),
            Token::OpenParen,
            Token::Id("n".into()),
            Token::CloseParen,
            Token::HasType,
            Token::Basic(BasicType::Int),
            Token::To,
            Token::Basic(BasicType::Int),
            Token::OpenBrac,
            Token::Statement(Stmt::If),
            Token::OpenParen,
            Token::Id("n".into()),
            Token::Op2(InfixOp::Smaller),
            Token::Number(2),
            Token::CloseParen,
            Token::OpenBrac,
            Token::Statement(Stmt::Return),
            Token::Number(1),
            Token::Terminal,
            Token::CloseBrac,
            Token::Statement(Stmt::Else),
            Token::OpenBrac,
            Token::Statement(Stmt::Return),
            Token::Id("n".into()),
            Token::Op2(InfixOp::Times),
            Token::Id("fac".into()),
            Token::OpenParen,
            Token::Id("n".into()),
            Token::Op2(InfixOp::Minus),
            Token::Number(1),
            Token::CloseParen,
            Token::Terminal,
            Token::CloseBrac,
            Token::CloseBrac,
        ];

        assert_eq!(tokens, expected)
    }
}
