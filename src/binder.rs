use error::Result;

use crate::scope::Scope;
use crate::tree::{Decl, SPL, Exp, FunDecl, Stmt};
use crate::binder::error::BindError;

pub trait Bindable<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()>;
}

impl<'a> Bindable<'a> for SPL<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        let mut errors = Vec::new();

        scope.open();
        errors.append(&mut self.decls.iter().flat_map(|decl| if let Decl::FunDecl(d) = decl { Some(d) } else { None }).flat_map(|d| scope.put_fun(d.id.clone(), d).err()).collect());
        errors.append(&mut self.decls.iter().flat_map(|decl| if let Decl::VarDecl(d) = decl { Some(d) } else { None }).flat_map(|d| scope.put_var(d.id.clone(), d).err()).collect());
        errors.append(&mut self.decls.iter().flat_map(|decl| decl.bind(scope).err()).flatten().collect());
        scope.close();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl<'a> Bindable<'a> for Decl<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        if let Decl::FunDecl(d) = self {
            d.bind(scope)
        } else {
            Ok(())
        }
    }
}

impl<'a> Bindable<'a> for FunDecl<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        let mut errors = Vec::new();

        // TODO: function argument scope

        scope.open();
        errors.append(&mut self.var_decls.iter().flat_map(|d| scope.put_var(d.id.clone(), d).err()).collect());
        errors.append(&mut self.stmts.iter().flat_map(|stmt| stmt.bind(scope).err()).flatten().collect());
        scope.close();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl<'a> Bindable<'a> for Stmt<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        let mut errors: Vec<BindError> = Vec::new();

        match self {
            Stmt::If(c, t, e) => {
                errors.append(&mut c.bind(scope).err().into_iter().flatten().collect());
                errors.append(&mut t.iter().flat_map(|stmt| stmt.bind(scope).err()).flatten().collect());
                errors.append(&mut e.iter().flat_map(|stmt| stmt.bind(scope).err()).flatten().collect());
            }
            Stmt::While(c, t) => {
                errors.append(&mut c.bind(scope).err().into_iter().flatten().collect());
                errors.append(&mut t.iter().flat_map(|stmt| stmt.bind(scope).err()).flatten().collect());
            }
            Stmt::Assignment(id, field, exp, reference) => {
                match scope.get_var(id) {
                    Ok(decl) => {
                        reference.borrow_mut().replace(decl);
                    }
                    Err(e) => errors.push(e)
                }
                errors.append(&mut exp.bind(scope).err().into_iter().flatten().collect());
            }
            Stmt::FunCall(fun_call, reference) => {
                match scope.get_fun(&fun_call.id) {
                    Ok(decl) => {
                        reference.borrow_mut().replace(decl);
                    }
                    Err(e) => errors.push(e)
                }
            }
            Stmt::Return(_) => {}
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

impl<'a> Bindable<'a> for Exp<'a> {
    fn bind(&'a self, scope: &mut Scope<'a>) -> Result<()> {
        let mut errors: Vec<BindError> = Vec::new();

        match self {
            Exp::Variable(id, field, reference) => {
                match scope.get_var(id) {
                    Ok(decl) => {
                        reference.borrow_mut().replace(decl);
                    }
                    Err(e) => errors.push(e)
                }
            }
            Exp::BinaryOp(_, lhs, rhs) => {
                errors.append(&mut lhs.bind(scope).err().into_iter().flatten().collect());
                errors.append(&mut rhs.bind(scope).err().into_iter().flatten().collect());
            }
            Exp::UnaryOp(_, rhs) => errors.append(&mut rhs.bind(scope).err().into_iter().flatten().collect()),
            Exp::FunCall(fun_call, reference) => {
                match scope.get_fun(&fun_call.id) {
                    Ok(decl) => {
                        reference.borrow_mut().replace(decl);
                    }
                    Err(e) => errors.push(e)
                }
            }
            Exp::Tuple(left, right) => {
                errors.append(&mut left.bind(scope).err().into_iter().flatten().collect());
                errors.append(&mut right.bind(scope).err().into_iter().flatten().collect());
            }
            Exp::Number(_) | Exp::Character(_) |  Exp::False | Exp::True | Exp::Nil => {}
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;
    use crate::tree::Id;

    pub type Result<T, E = Vec<BindError>> = std::result::Result<T, E>;

    pub enum BindError {
        UnresolvedReference(Id),
        Redefined(Id)
    }

    impl fmt::Display for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                BindError::UnresolvedReference(r) => write!(f, "Unresolved reference: {}", r),
                BindError::Redefined(r) => write!(f, "Identifier {} is defined multiple times in this scope", r)
            }
        }
    }

    impl Debug for BindError {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for BindError {}
}
