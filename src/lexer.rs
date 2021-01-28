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
