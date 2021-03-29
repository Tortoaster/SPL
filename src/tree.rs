use crate::lexer::{Field, Operator};

#[derive(Debug, Eq, PartialEq)]
pub struct SPL {
    pub decls: Vec<Decl>
}

#[derive(Debug, Eq, PartialEq)]
pub enum Decl {
    VarDecl(VarDecl),
    FunDecl(FunDecl),
}

#[derive(Debug, Eq, PartialEq)]
pub struct VarDecl {
    pub var_type: VarType,
    pub id: Id,
    pub exp: Exp
}

#[derive(Debug, Eq, PartialEq)]
pub enum VarType {
    Var,
    Type(Type),
}

#[derive(Debug, Eq, PartialEq)]
pub struct FunDecl {
    pub id: Id,
    pub args: Vec<Id>,
    pub fun_type: Option<FunType>,
    pub var_decls: Vec<VarDecl>,
    pub stmts: Vec<Stmt>
}

#[derive(Debug, Eq, PartialEq)]
pub struct FunType {
    pub arg_types: Vec<Type>,
    pub ret_type: RetType
}

#[derive(Debug, Eq, PartialEq)]
pub enum RetType {
    Type(Type),
    Void,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Type {
    BasicType(BasicType),
    Tuple(Box<Type>, Box<Type>),
    Array(Box<Type>),
    Generic(Id),
}

#[derive(Debug, Eq, PartialEq)]
pub enum BasicType {
    Int,
    Bool,
    Char,
}

#[derive(Debug, Eq, PartialEq)]
pub enum Stmt {
    If(Exp, Vec<Stmt>, Vec<Stmt>),
    While(Exp, Vec<Stmt>),
    Assignment(Id, Selector, Exp),
    FunCall(FunCall),
    Return(Option<Exp>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Exp {
    Variable(Id),
    BinaryOp(Operator, Box<Exp>, Box<Exp>),
    UnaryOp(Operator, Box<Exp>),
    Number(i32),
    Character(char),
    False,
    True,
    FunCall(FunCall),
    Nil,
    Tuple(Box<Exp>, Box<Exp>),
}

#[derive(Debug, Eq, PartialEq)]
pub struct Selector {
    pub fields: Vec<Field>
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FunCall {
    pub id: Id,
    pub args: Vec<Exp>
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Id(pub String);

mod printer {
    use std::fmt;

    use super::{BasicType, Decl, Exp, FunCall, FunDecl, FunType, Id, RetType, Selector, SPL, Stmt, Type, VarDecl, VarType};

    const TAB_SIZE: usize = 4;

    trait PrettyPrintable {
        fn fmt_pretty(&self, indent: usize) -> String;
    }

    impl fmt::Display for SPL {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.fmt_pretty(0))
        }
    }

    impl PrettyPrintable for SPL {
        fn fmt_pretty(&self, indent: usize) -> String {
            self.decls.iter().map(|decl| decl.fmt_pretty(indent)).collect::<Vec<String>>().join("\n")
        }
    }

    impl PrettyPrintable for Decl {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Decl::VarDecl(var) => var.fmt_pretty(indent),
                Decl::FunDecl(fun) => fun.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for VarDecl {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{:indent$}{} {} = {};\n",
                    "",
                    self.var_type.fmt_pretty(indent),
                    self.id.fmt_pretty(indent),
                    self.exp.fmt_pretty(indent),
                    indent = indent * TAB_SIZE
            )
        }
    }

    impl PrettyPrintable for VarType {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                VarType::Var => String::from("var"),
                VarType::Type(t) => t.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for FunDecl {
        fn fmt_pretty(&self, indent: usize) -> String {
            let mut f = format!("{:indent$}{}({}) ",
                                "",
                                self.id.fmt_pretty(indent),
                                self.args.iter().map(|id| id.fmt_pretty(indent)).collect::<Vec<String>>().join(", "),
                                indent = indent * TAB_SIZE
            );
            if let Some(fun_type) = &self.fun_type {
                f += fun_type.fmt_pretty(indent).as_str();
            }
            f += format!("{{\n").as_str();
            f += self.var_decls.iter().map(|var| var.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f += self.stmts.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
        }
    }

    impl PrettyPrintable for FunType {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!(":: {}-> {} ",
                    self.arg_types.iter().map(|t| t.fmt_pretty(indent) + " ").collect::<Vec<String>>().join(""),
                    self.ret_type.fmt_pretty(indent)
            )
        }
    }

    impl PrettyPrintable for RetType {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                RetType::Type(t) => t.fmt_pretty(indent),
                RetType::Void => String::from("Void"),
            }
        }
    }

    impl PrettyPrintable for Type {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Type::BasicType(t) => t.fmt_pretty(indent),
                Type::Tuple(l, r) => format!("({}, {})", l.fmt_pretty(indent), r.fmt_pretty(indent)),
                Type::Array(t) => format!("[{}]", t.fmt_pretty(indent)),
                Type::Generic(t) => t.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for BasicType {
        fn fmt_pretty(&self, _: usize) -> String {
            match self {
                BasicType::Int => String::from("Int"),
                BasicType::Bool => String::from("Bool"),
                BasicType::Char => String::from("Char"),
            }
        }
    }

    impl PrettyPrintable for Stmt {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Stmt::If(condition, then, otherwise) => {
                    let mut f = format!("{:indent$}if ({}) {{\n",
                                        "",
                                        condition.fmt_pretty(indent),
                                        indent = indent * TAB_SIZE
                    );
                    f += then.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    if !otherwise.is_empty() {
                        f += format!("{:indent$}}} else {{\n", "", indent = indent * TAB_SIZE).as_str();
                        f += otherwise.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    }
                    f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
                }
                Stmt::While(condition, body) => {
                    let mut f = format!("{:indent$}while ({}) {{\n",
                                        "",
                                        condition.fmt_pretty(indent),
                                        indent = indent * TAB_SIZE
                    );
                    f += body.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
                    f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
                }
                Stmt::Assignment(id, field, value) => format!("{:indent$}{}{} = {};\n",
                                                              "",
                                                              id.fmt_pretty(indent),
                                                              field.fmt_pretty(indent),
                                                              value.fmt_pretty(indent),
                                                              indent = indent * TAB_SIZE
                ),
                Stmt::FunCall(fun_call) => format!("{:indent$}{};\n",
                                                   "",
                                                   fun_call.fmt_pretty(indent),
                                                   indent = indent * TAB_SIZE
                ),
                Stmt::Return(value) => match value {
                    None => format!("{:indent$}return;\n", "", indent = indent * TAB_SIZE),
                    Some(ret) => format!("{:indent$}return {};\n", "", ret.fmt_pretty(indent), indent = indent * TAB_SIZE),
                }
            }
        }
    }

    impl PrettyPrintable for Exp {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Exp::Variable(id) => id.fmt_pretty(indent),
                Exp::BinaryOp(op, lhs, rhs) => format!("({} {} {})", lhs.fmt_pretty(indent), op, rhs.fmt_pretty(indent)),
                Exp::UnaryOp(op, lhs) => format!("({}{})", op, lhs.fmt_pretty(indent)),
                Exp::Number(n) => format!("{}", n),
                Exp::Character(c) => format!("'{}'", c),
                Exp::False => format!("False"),
                Exp::True => format!("True"),
                Exp::FunCall(fun_call) => format!("{}", fun_call.fmt_pretty(indent)),
                Exp::Nil => format!("[]"),
                Exp::Tuple(l, r) => format!("({}, {})", l.fmt_pretty(indent), r.fmt_pretty(indent)),
            }
        }
    }

    impl PrettyPrintable for Selector {
        fn fmt_pretty(&self, _: usize) -> String {
            self.fields.iter().map(|field| ".".to_owned() + format!("{}", field).as_str()).collect::<Vec<String>>().join("")
        }
    }

    impl PrettyPrintable for FunCall {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{}({})",
                    self.id.fmt_pretty(indent),
                    self.args.iter().map(|exp| exp.fmt_pretty(indent)).collect::<Vec<String>>().join(", ")
            )
        }
    }

    impl PrettyPrintable for Id {
        fn fmt_pretty(&self, _: usize) -> String {
            self.0.clone()
        }
    }
}
