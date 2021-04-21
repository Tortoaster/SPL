use std::fmt;

use crate::algorithm_w::{Space, Type};
use crate::lexer::Field;

#[derive(Debug, Eq, PartialEq)]
pub struct SPL {
    pub decls: Vec<Decl>
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Decl {
    VarDecl(VarDecl),
    FunDecl(FunDecl),
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct VarDecl {
    pub var_type: Option<Type>,
    pub id: Id,
    pub exp: Exp,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct FunDecl {
    pub id: Id,
    pub args: Vec<Id>,
    pub fun_type: Option<Type>,
    pub var_decls: Vec<VarDecl>,
    pub stmts: Vec<Stmt>,
}

#[derive(Debug, Eq, PartialEq, Hash)]
pub enum Stmt {
    If(Exp, Vec<Stmt>, Vec<Stmt>),
    While(Exp, Vec<Stmt>),
    Assignment(Id, Vec<Field>, Exp),
    FunCall(FunCall),
    Return(Option<Exp>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Exp {
    Variable(Id),
    Number(i32),
    Character(char),
    False,
    True,
    FunCall(FunCall),
    Nil,
    Tuple(Box<Exp>, Box<Exp>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunCall {
    pub id: Id,
    pub args: Vec<Exp>,
    pub call_type: Option<Type>
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Id(pub String);

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Decl {
    pub fn id(&self) -> Id {
        match self {
            Decl::VarDecl(decl) => decl.id.clone(),
            Decl::FunDecl(decl) => decl.id.clone()
        }
    }

    pub fn space(&self) -> Space {
        match self {
            Decl::VarDecl(_) => Space::Var,
            Decl::FunDecl(_) => Space::Fun
        }
    }
}

mod printer {
    use std::fmt;

    use crate::lexer::Field;

    use super::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
    use crate::algorithm_w::{Type, Environment};

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

    /// Pretty printer for variable type annotations
    impl PrettyPrintable for Option<Type> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                None => String::from("var"),
                Some(t) => t.fmt_pretty(indent),
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
                f += format!(":: ").as_str();
                match fun_type {
                    Type::Function(_, _) => f += fun_type.fmt_pretty(indent).as_str(),
                    _ => f += format!("-> {}", fun_type.fmt_pretty(indent)).as_str()
                }
            }
            f += format!(" {{\n").as_str();
            f += self.var_decls.iter().map(|var| var.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f += self.stmts.iter().map(|stmt| stmt.fmt_pretty(indent + 1)).collect::<Vec<String>>().join("").as_str();
            f + format!("{:indent$}}}\n", "", indent = indent * TAB_SIZE).as_str()
        }
    }

    impl PrettyPrintable for Type {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{:indent$}{}", "", self.generalize(&Environment::new()), indent = indent * TAB_SIZE)
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
                Stmt::Assignment(id, fields, value) => format!("{:indent$}{}{} = {};\n",
                                                               "",
                                                               id.fmt_pretty(indent),
                                                               fields.fmt_pretty(indent),
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

    impl PrettyPrintable for Vec<Field> {
        fn fmt_pretty(&self, _: usize) -> String {
            self.iter().map(|field| ".".to_owned() + format!("{}", field).as_str()).collect::<Vec<String>>().join("")
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
