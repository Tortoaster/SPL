use std::str::Chars;
use std::iter::Peekable;

#[derive(Debug)]
pub enum BasicType {
    Int, // Int
    Bool, // Bool
    Char, // Char
}

#[derive(Debug)]
pub enum Stmt {
    If, // if
    While, // while
    Return, // return
}

#[derive(Debug)]
pub enum Expr {
    False, // False,
    True, // True,
    Nil, // []
}

#[derive(Debug)]
pub enum Field {
    Dot, // .
    Head, // hd
    Tail, // tl
    First, // fst
    Second, // snd
}

#[derive(Debug)]
pub enum Op2 {
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

#[derive(Debug)]
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
    Returns, // ->
    Separator, // ,
    OpenArr, // [
    CloseArr, // ]
    Basic(BasicType),
    Statement(Stmt),
    Expression(Expr),
    Field(Field),
    Not, // !
    Op2(Op2),
    Num(i32),
    Id(String),
}

pub trait Tokenize {
    fn tokenize(&self) -> Scanner<'_>;
}

impl Tokenize for &str {
    fn tokenize(&self) -> Scanner<'_> {
        Scanner {
            chars: self.chars().peekable()
        }
    }
}

pub struct Scanner<'a> {
    chars: Peekable<Chars<'a>>
}

impl Scanner<'_> {
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

    fn read_num(&mut self, start: Option<char>) -> i32 {
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

    fn abort(&mut self) -> Token {
        panic!("Unexpected character '{:?}' at {}:{}", self.chars.peek(), 0, 0)
    }
}

impl Iterator for Scanner<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        let current = self.chars.next()?;

        Some(
            match current {
                '+' => Token::Op2(Op2::Plus),
                '-' => {
                    if let Some(c) = self.chars.peek() {
                        if c.is_ascii_digit() {
                            Token::Num(-self.read_num(None))
                        } else {
                            Token::Op2(Op2::Minus)
                        }
                    } else {
                        self.abort()
                    }
                },
                '*' => Token::Op2(Op2::Times),
                '/' => Token::Op2(Op2::Divide),
                '%' => Token::Op2(Op2::Modulo),
                '=' => {
                    if self.followed_by('=') {
                        Token::Op2(Op2::Equals)
                    } else {
                        Token::Assign
                    }
                }
                '<' => {
                    if self.followed_by('=') {
                        Token::Op2(Op2::SmallerEqual)
                    } else {
                        Token::Op2(Op2::Smaller)
                    }
                }
                '>' => {
                    if self.followed_by('=') {
                        Token::Op2(Op2::SmallerEqual)
                    } else {
                        Token::Op2(Op2::Smaller)
                    }
                }
                '!' => {
                    if self.followed_by('=') {
                        Token::Op2(Op2::NotEqual)
                    } else {
                        Token::Not
                    }
                }
                '&' => {
                    if self.followed_by('&') {
                        Token::Op2(Op2::And)
                    } else {
                        self.abort()
                    }
                }
                '|' => {
                    if self.followed_by('|') {
                        Token::Op2(Op2::Or)
                    } else {
                        self.abort()
                    }
                }
                ':' => Token::Op2(Op2::Cons),
                '[' => {
                    if self.followed_by(']') {
                        Token::Expression(Expr::Nil)
                    } else {
                        Token::OpenArr
                    }
                }
                ']' => Token::CloseArr,
                '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => {
                    Token::Num(self.read_num(Some(current)))
                }
                ' ' | '\n' | '\t' => {
                    return self.next();
                }
                _ => self.abort()
            }
        )
    }
}
