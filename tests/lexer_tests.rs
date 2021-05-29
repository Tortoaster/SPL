use spl::lexer::{Lexable, Operator, Token};

#[test]
fn nested_comments() {
    let code = "
    /* fac(n) :: Int -> Int {
        /* if (n < 2) {
            return 1;
        } else {
            return n * fac(n - 1);
        } */
    } */
    ";
    let tokens: Vec<Token> = code.tokenize().expect("Failed to tokenize").map(|p| p.content).collect();
    assert!(tokens.is_empty())
}

#[test]
fn fac() {
    let code = "
    fac(n) :: Int -> Int {
        if (n < 2) {
            return 1;
        } else {
            return n * fac(n - 1);
        }
    }
    ";
    let tokens: Vec<Token> = code.tokenize().expect("Failed to tokenize").map(|p| p.content).collect();
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
