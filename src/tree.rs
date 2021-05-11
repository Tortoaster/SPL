use std::collections::BTreeMap;
use std::fmt;

use crate::algorithm_w::{PolyType, Space, Type, TypeVariable};
use crate::lexer::Field;
use crate::position::Pos;

type PDecl<'a> = Pos<'a, Decl<'a>>;
type PVarDecl<'a> = Pos<'a, VarDecl<'a>>;
pub type PStmt<'a> = Pos<'a, Stmt<'a>>;
type PExp<'a> = Pos<'a, Exp<'a>>;
type PField<'a> = Pos<'a, Field>;
type PId<'a> = Pos<'a, Id>;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SPL<'a> {
    pub decls: Vec<PDecl<'a>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Decl<'a> {
    VarDecl(VarDecl<'a>),
    FunDecl(FunDecl<'a>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct VarDecl<'a> {
    // TODO: PolyType instead?
    pub var_type: Pos<'a, Option<Type>>,
    pub id: PId<'a>,
    pub exp: PExp<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunDecl<'a> {
    pub id: PId<'a>,
    pub args: Vec<PId<'a>>,
    pub fun_type: Option<Pos<'a, PolyType>>,
    pub var_decls: Vec<PVarDecl<'a>>,
    pub stmts: Vec<PStmt<'a>>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Stmt<'a> {
    If(PExp<'a>, Vec<PStmt<'a>>, Vec<PStmt<'a>>),
    While(PExp<'a>, Vec<PStmt<'a>>),
    Assignment(PId<'a>, Vec<PField<'a>>, PExp<'a>),
    FunCall(FunCall<'a>),
    Return(Option<PExp<'a>>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub enum Exp<'a> {
    Variable(Id),
    Number(i32),
    Character(char),
    Boolean(bool),
    FunCall(FunCall<'a>),
    Nil,
    Tuple(Box<PExp<'a>>, Box<PExp<'a>>),
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct FunCall<'a> {
    pub id: PId<'a>,
    pub args: Vec<PExp<'a>>,
    pub type_args: BTreeMap<TypeVariable, Type>,
}

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Id(pub String);

impl fmt::Display for Id {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Decl<'_> {
    pub fn id(&self) -> Id {
        match self {
            Decl::VarDecl(decl) => decl.id.inner.clone(),
            Decl::FunDecl(decl) => decl.id.inner.clone()
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

    use crate::algorithm_w::{Environment, PolyType, Type};
    use crate::tree::PField;

    use super::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};

    const TAB_SIZE: usize = 4;

    trait PrettyPrintable {
        fn fmt_pretty(&self, indent: usize) -> String;
    }

    impl fmt::Display for SPL<'_> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self.fmt_pretty(0))
        }
    }

    impl PrettyPrintable for SPL<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            self.decls.iter().map(|decl| decl.fmt_pretty(indent)).collect::<Vec<String>>().join("\n")
        }
    }

    impl PrettyPrintable for Decl<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Decl::VarDecl(var) => var.fmt_pretty(indent),
                Decl::FunDecl(fun) => fun.fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for VarDecl<'_> {
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
                Some(t) => t.generalize(&Environment::new()).fmt_pretty(indent),
            }
        }
    }

    impl PrettyPrintable for FunDecl<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            let mut f = format!("{:indent$}{}({}) ",
                                "",
                                self.id.fmt_pretty(indent),
                                self.args.iter().map(|id| id.fmt_pretty(indent)).collect::<Vec<String>>().join(", "),
                                indent = indent * TAB_SIZE
            );
            if let Some(fun_type) = &self.fun_type {
                f += format!(":: ").as_str();
                match fun_type.inner.inner {
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

    impl PrettyPrintable for PolyType {
        fn fmt_pretty(&self, indent: usize) -> String {
            format!("{:indent$}{}", "", self, indent = indent * TAB_SIZE)
        }
    }

    impl PrettyPrintable for Stmt<'_> {
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

    impl PrettyPrintable for Exp<'_> {
        fn fmt_pretty(&self, indent: usize) -> String {
            match self {
                Exp::Variable(id) => id.fmt_pretty(indent),
                Exp::Number(n) => format!("{}", n),
                Exp::Character(c) => format!("'{}'", c),
                Exp::Boolean(b) => format!("{}", b),
                Exp::FunCall(fun_call) => format!("{}", fun_call.fmt_pretty(indent)),
                Exp::Nil => format!("[]"),
                Exp::Tuple(l, r) => format!("({}, {})", l.fmt_pretty(indent), r.fmt_pretty(indent)),
            }
        }
    }

    impl PrettyPrintable for Vec<PField<'_>> {
        fn fmt_pretty(&self, _: usize) -> String {
            self.iter().map(|field| ".".to_owned() + format!("{}", field.inner).as_str()).collect::<Vec<String>>().join("")
        }
    }

    impl PrettyPrintable for FunCall<'_> {
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
