use std::fs;

use spl::lexer::{Operator, Token, Lexable};

const RES_DIR: &str = "tests/res/";

#[test]
fn fac() {
    let code = fs::read_to_string(RES_DIR.to_owned() + "fac.spl").expect("File inaccessible");
    let tokens: Vec<Token> = code.as_str().tokenize().collect();
    let expected = vec![
        Token::Identifier("fac".into()),
        Token::OpenParen,
        Token::Identifier("n".into()),
        Token::CloseParen,
        Token::HasType,
        Token::Int,
        Token::To,
        Token::Int,
        Token::OpenBracket,
        Token::If,
        Token::OpenParen,
        Token::Identifier("n".into()),
        Token::Operator(Operator::Smaller),
        Token::Number(2),
        Token::CloseParen,
        Token::OpenBracket,
        Token::Return,
        Token::Number(1),
        Token::Semicolon,
        Token::CloseBracket,
        Token::Else,
        Token::OpenBracket,
        Token::Return,
        Token::Identifier("n".into()),
        Token::Operator(Operator::Times),
        Token::Identifier("fac".into()),
        Token::OpenParen,
        Token::Identifier("n".into()),
        Token::Operator(Operator::Minus),
        Token::Number(1),
        Token::CloseParen,
        Token::Semicolon,
        Token::CloseBracket,
        Token::CloseBracket,
    ];

    assert_eq!(tokens, expected)
}
