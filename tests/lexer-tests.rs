#[cfg(test)]
mod tests {
    use std::fs;

    use SPL::lexer::{BasicType, Op, Stmt, Token, Tokenize};
    use SPL::lexer;

    #[test]
    fn lex_fac() {
        let code = fs::read_to_string("tests/fac.spl").expect("File inaccessible");
        let tokens: Vec<Token> = code.tokenize().collect();
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
            Token::Operation(Op::Smaller),
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
            Token::Operation(Op::Times),
            Token::Id("fac".into()),
            Token::OpenParen,
            Token::Id("n".into()),
            Token::Operation(Op::Minus),
            Token::Number(1),
            Token::CloseParen,
            Token::Terminal,
            Token::CloseBrac,
            Token::CloseBrac,
        ];

        assert_eq!(tokens, expected)
    }
}
