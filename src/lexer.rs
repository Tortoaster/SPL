use std::str::Chars;
use std::iter::Peekable;

enum BasicType {
    Int, // Int
    Bool, // Bool
    Char, // Char
}

enum Stmt {
    If, // if
    While, // while
    Return, // return
}

enum Expr {
    False, // False,
    True, // True,
    Nil, // []
}

enum Field {
    Dot, // .
    Head, // hd
    Tail, // tl
    First, // fst
    Second, // snd
}

enum Op2 {
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

enum Op1 {
    Not, // !
    UnaryMinus, // -
}

enum Token {
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
    Op1(Op1),
    Op2(Op2),
    Num(i32),
    Id(String),
}

struct Scanner<'a> {
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

    fn abort(&mut self) -> Token {
        panic!("Unexpected token '{:?}' at {}:{}", self.chars.peek(), 0, 0)
    }
}

impl Iterator for Scanner<'_> {
    type Item = Token;

    fn next(&mut self) -> Option<Token> {
        Some(
            match self.chars.next()? {
                '+' => Token::Op2(Op2::Plus),
                '-' => Token::Op2(Op2::Minus),
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
                        Token::Op1(Op1::Not)
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
                _ => self.abort()
            }
        )
    }
}
