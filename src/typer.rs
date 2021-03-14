use std::fmt;
use std::error::Error;
use std::fmt::Debug;

// type Result<T, E = TypeError> = std::result::Result<T, E>;

enum TypeError {
    TypeMismatch
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeError::TypeMismatch => write!(f, "Type mismatch")
        }
    }
}

impl Debug for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self)
    }
}

impl Error for TypeError {}

enum Type {
    Int,
    Bool,
    Char,
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Polymorphic(String)
}

trait Inferrable {
    fn infer_type(&self) -> Type;
}

// impl Inferrable for Exp {
//     fn infer_type(&self) -> Type {
//         match self {
//             Exp::Identifier(_, _) => {}
//             Exp::BinaryOp(_, _, _) => {}
//             Exp::UnaryOp(_, _) => {}
//             Exp::Number(_) => {}
//             Exp::Character(_) => {}
//             Exp::False => {}
//             Exp::True => {}
//             Exp::FunCall(_) => {}
//             Exp::Nil => {}
//             Exp::Tuple(_, _) => {}
//         }
//     }
// }
