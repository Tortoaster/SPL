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

#[derive(Debug, Eq, PartialEq)]
pub enum Op {
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
    Not, // !
    Operation(Op),
    Number(i32),
    Character(char),
    Id(String),
}

pub trait Tokenize {
    fn tokenize(&self) -> Scanner<'_>;
}

impl Tokenize for String {
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

    fn followed_by_str(&mut self, s: &str) -> bool {
        s.chars().all(|c|
            match self.chars.peek() {
                None => false,
                Some(d) => if c == *d {
                    self.chars.next();
                    true
                } else {
                    false
                }
            }
        )
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

    fn read_id(&mut self, start: char) -> String {
        let mut alpha_numericals = vec![start];

        while let Some(c) = self.chars.peek() {
            if c.is_alphanumeric() {
                alpha_numericals.push(self.chars.next().unwrap())
            } else {
                break;
            }
        }

        alpha_numericals.into_iter().collect()
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
                '+' => Token::Operation(Op::Plus),
                '-' => if self.followed_by('>') {
                    Token::To
                } else if let Some(c) = self.chars.peek() {
                    if c.is_ascii_digit() {
                        Token::Number(-self.read_num(None))
                    } else {
                        Token::Operation(Op::Minus)
                    }
                } else {
                    self.abort()
                }
                '*' => Token::Operation(Op::Times),
                '/' => Token::Operation(Op::Divide),
                '%' => Token::Operation(Op::Modulo),
                '=' => if self.followed_by('=') {
                    Token::Operation(Op::Equals)
                } else {
                    Token::Assign
                }
                '<' => if self.followed_by('=') {
                    Token::Operation(Op::SmallerEqual)
                } else {
                    Token::Operation(Op::Smaller)
                }
                '>' => if self.followed_by('=') {
                    Token::Operation(Op::GreaterEqual)
                } else {
                    Token::Operation(Op::Greater)
                }
                '!' => if self.followed_by('=') {
                    Token::Operation(Op::NotEqual)
                } else {
                    Token::Not
                }
                '&' => if self.followed_by('&') {
                    Token::Operation(Op::And)
                } else {
                    self.abort()
                }
                '|' => if self.followed_by('|') {
                    Token::Operation(Op::Or)
                } else {
                    self.abort()
                }
                ':' => if self.followed_by(':') {
                    Token::HasType
                } else {
                    Token::Operation(Op::Cons)
                }
                '[' => if self.followed_by(']') {
                    Token::Expression(Expr::Nil)
                } else {
                    Token::OpenArr
                }
                ']' => Token::CloseArr,
                '.' => Token::Field(Field::Dot),
                'h' => if self.followed_by('d') {
                    Token::Field(Field::Head)
                } else {
                    Token::Id(self.read_id(current))
                }
                't' => if self.followed_by('l') {
                    Token::Field(Field::Tail)
                } else {
                    Token::Id(self.read_id(current))
                }
                'f' => if self.followed_by_str("st") {
                    Token::Field(Field::First)
                } else {
                    Token::Id(self.read_id(current))
                }
                's' => if self.followed_by_str("nd") {
                    Token::Field(Field::Second)
                } else {
                    Token::Id(self.read_id(current))
                }
                'F' => if self.followed_by_str("alse") {
                    Token::Expression(Expr::False)
                } else {
                    Token::Id(self.read_id(current))
                }
                'T' => if self.followed_by_str("rue") {
                    Token::Expression(Expr::True)
                } else {
                    Token::Id(self.read_id(current))
                }
                'i' => if self.followed_by('f') {
                    Token::Statement(Stmt::If)
                } else {
                    Token::Id(self.read_id(current))
                }
                'e' => if self.followed_by_str("lse") {
                    Token::Statement(Stmt::Else)
                } else {
                    Token::Id(self.read_id(current))
                }
                'w' => if self.followed_by_str("hile") {
                    Token::Statement(Stmt::While)
                } else {
                    Token::Id(self.read_id(current))
                }
                'r' => if self.followed_by_str("eturn") {
                    Token::Statement(Stmt::Return)
                } else {
                    Token::Id(self.read_id(current))
                }
                'I' => if self.followed_by_str("nt") {
                    Token::Basic(BasicType::Int)
                } else {
                    Token::Id(self.read_id(current))
                }
                'B' => if self.followed_by_str("ool") {
                    Token::Basic(BasicType::Bool)
                } else {
                    Token::Id(self.read_id(current))
                }
                'C' => if self.followed_by_str("har") {
                    Token::Basic(BasicType::Char)
                } else {
                    Token::Id(self.read_id(current))
                }
                'v' => if self.followed_by_str("ar") {
                    Token::Var
                } else {
                    Token::Id(self.read_id(current))
                }
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
                ';' => Token::Terminal,
                '(' => Token::OpenParen,
                ')' => Token::CloseParen,
                '{' => Token::OpenBrac,
                '}' => Token::CloseBrac,
                'V' => if self.followed_by_str("oid") {
                    Token::Void
                } else {
                    Token::Id(self.read_id(current))
                }
                ',' => Token::Separator,
                '0'..='9' => Token::Number(self.read_num(Some(current))),
                'a'..='z' | 'A'..='Z' => Token::Id(self.read_id(current)),
                ' ' | '\r' | '\n' | '\t' => return self.next(),
                _ => panic!("Invalid character '{:?}' at {}:{}", current, 0, 0)
            }
        )
    }
}
