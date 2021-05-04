use std::collections::{HashMap, HashSet};
use std::fmt;

use error::Result;

use crate::algorithm_w::{Space, Type};
use crate::generator::error::GenError;
use crate::ssm::prelude::*;
// Reserve first scratch register to keep track of global variables
use crate::ssm::Register::R0 as GP;
use crate::tree::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
use crate::typer::DecoratedSPL;

const MAIN: &str = "main";

struct Scope {
    globals: HashMap<Id, Vec<Instruction>>,
    locals: HashMap<Id, Vec<Instruction>>,
    arguments: HashMap<Id, Vec<Instruction>>,
    functions: HashMap<FunCall, Vec<Instruction>>,
}

impl Scope {
    fn new() -> Self {
        Scope {
            globals: HashMap::new(),
            locals: HashMap::new(),
            arguments: HashMap::new(),
            functions: HashMap::new(),
        }
    }

    fn push_var(&self, id: &Id) -> Vec<Instruction> {
        self.locals
            .get(id)
            .or(self.arguments.get(id))
            .or(self.globals.get(id))
            .unwrap()
            .clone()
    }
}

impl DecoratedSPL {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate(&mut Scope::new())?.0 })
    }
}

pub struct Program {
    instructions: Vec<Instruction>,
}

impl fmt::Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for i in &self.instructions {
            writeln!(f, "{}", i)?;
        }
        Ok(())
    }
}

trait Gen {
    fn generate(&self, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)>;
}

trait GenIndex {
    fn generate_indexed(&self, index: isize, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)>;
}

impl Gen for SPL {
    fn generate(&self, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        // Reserve space for global variables
        let globals = self.decls
            .iter()
            .filter(|decl| decl.space() == Space::Var)
            .count();
        let mut instructions = vec![
            Link { length: globals },
            LoadRegisterFromRegister { from: SP, to: GP }
        ];

        // Generate code to initialize global variables
        let (mut variables, var_variants) = self.decls
            .iter()
            .enumerate()
            .map(|(index, decl)| match decl {
                Decl::VarDecl(var_decl) => var_decl.generate_global(index as isize, scope),
                _ => Ok((Vec::new(), HashSet::new()))
            })
            .collect::<Result<Vec<(Vec<Instruction>, HashSet<(Id, Type)>)>>>()?
            .into_iter()
            .fold((Vec::new(), HashSet::new()), |(inst, variants), (new_inst, new_variants)|
                (inst.into_iter().chain(new_inst).collect(),
                 variants.into_iter().chain(new_variants).collect()),
            );
        instructions.append(&mut variables);

        // Move to main function, halt when it returns
        instructions.push(BranchSubroutine { label: Label::new(MAIN) });
        instructions.push(Halt);

        // Generate code for main function
        let (mut functions, fun_variants) = self.decls
            .iter()
            .find_map(|decl| match decl {
                Decl::FunDecl(fun_decl) => (fun_decl.id == Id(MAIN.to_owned())).then(|| fun_decl),
                _ => None
            })
            .ok_or(GenError::MissingMain)?
            .generate(scope)?;
        instructions.append(&mut functions);

        let variants: HashSet<(Id, Type)> = var_variants.into_iter().chain(fun_variants).collect();

        // Keep generating necessary variants until all are done
        while !variants.is_empty() {}

        // Generate core functions
        instructions.append(&mut core::core());

        Ok((instructions, variants))
    }
}

impl VarDecl {
    fn generate_global(&self, index: isize, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        let offset = -index - 1;

        // Initialization
        let (mut instructions, deps) = self.exp.generate(scope)?;
        instructions.push(LoadRegister { reg: GP });
        instructions.push(StoreByAddress { offset });

        // Retrieving
        scope.globals.insert(self.id.clone(), vec![
            LoadRegister { reg: GP },
            LoadAddress { offset }
        ]);

        Ok((instructions, deps))
    }

    fn generate_local(&self, index: isize, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        let offset = index + 1;
        // Initialization
        let (mut instructions, deps) = self.exp.generate(scope)?;

        // Retrieving
        scope.locals.insert(self.id.clone(), vec![LoadLocal { offset }]);

        Ok((instructions, deps))
    }
}

impl Gen for FunDecl {
    fn generate(&self, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        let mut instructions = Vec::new();

        instructions.push(Labeled(Label::new(&self.id.to_string()), Box::new(Link { length: self.var_decls.len() })));
        for (index, var) in self.var_decls.iter().enumerate() {
            let (mut vars, _) = var.generate_local(index as isize, scope)?;
            instructions.append(&mut vars);
        }
        for stmt in &self.stmts {
            let (mut stmts, _) = stmt.generate(scope)?;
            instructions.append(&mut stmts);
        }
        instructions.push(Unlink);
        instructions.push(Return);

        Ok((instructions, HashSet::new()))
    }
}

impl Gen for Stmt {
    fn generate(&self, _: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        let instructions = match self {
            Stmt::If(_, _, _) => vec![Nop],
            Stmt::While(_, _) => vec![Nop],
            Stmt::Assignment(_, _, _) => vec![Nop],
            Stmt::FunCall(_) => vec![Nop],
            Stmt::Return(_) => vec![Nop],
        };

        Ok((instructions, HashSet::new()))
    }
}

/// Generates an expression, leaving the result on top of the stack
impl Gen for Exp {
    fn generate(&self, scope: &mut Scope) -> Result<(Vec<Instruction>, HashSet<(Id, Type)>)> {
        let instructions = match self {
            Exp::Variable(id) => scope.push_var(id),
            Exp::Number(n) => vec![LoadConstant(*n)],
            Exp::Character(c) => vec![LoadConstant(*c as i32)],
            Exp::False => vec![LoadConstant(0)],
            Exp::True => vec![LoadConstant(-1)],
            Exp::FunCall(fun_call) => {
                // Evaluate arguments
                fun_call.args
                    .iter()
                    .map(|arg| arg.generate(scope))
                    .collect::<Result<Vec<(Vec<Instruction>, HashSet<(Id, Type)>)>>>()?
                    .into_iter()
                    .flat_map(|(instructions, _)| instructions)
                    .chain(vec![
                        // Branch to function
                        BranchSubroutine { label: Label::new(fun_call.identifier()) },
                        // Remove arguments
                        AdjustStack { offset: -(fun_call.args.len() as isize) },
                        // Push result
                        LoadRegister { reg: RR }
                    ])
                    .collect()
            }
            Exp::Nil => vec![LoadConstant(0)],
            Exp::Tuple(l, r) => {
                let (mut x, _) = l.generate(scope)?;
                let (mut y, _) = r.generate(scope)?;
                x.append(&mut y);
                x
            }
        };

        Ok((instructions, HashSet::new()))
    }
}

impl FunCall {
    fn identifier(&self) -> &str {
        self.id.0.as_str()
    }
}

mod core {
    use crate::ssm::prelude::*;

    pub fn core() -> Vec<Instruction> {
        std::iter::empty()
            .chain(print_char())
            .chain(print_int())
            .chain(print_bool())
            .chain(eq_char())
            .chain(eq_int())
            .chain(eq_bool())
            .chain(lt_char())
            .chain(lt_int())
            .chain(gt_char())
            .chain(gt_int())
            .chain(le_char())
            .chain(le_int())
            .chain(ge_char())
            .chain(ge_int())
            .collect()
    }

    fn print_char() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("print$char"), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintChar },
            Return
        ]
    }

    fn print_int() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("print$int"), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintInt },
            Return
        ]
    }

    fn print_bool() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("print$int"), Box::new(LoadStack { offset: -1 })),
            BranchFalse { label: Label::new("print$int-else1") },
            LoadConstant('T' as i32),
            Trap { call: PrintChar },
            LoadConstant('r' as i32),
            Trap { call: PrintChar },
            LoadConstant('u' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Branch { label: Label::new("print$int-endif1") },
            Labeled(Label::new("print$int-else1"), Box::new(LoadConstant('F' as i32))),
            Trap { call: PrintChar },
            LoadConstant('a' as i32),
            Trap { call: PrintChar },
            LoadConstant('l' as i32),
            Trap { call: PrintChar },
            LoadConstant('s' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Labeled(Label::new("print$int-endif1"), Box::new(Return)),
        ]
    }

    fn eq_char() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("eq$char"), Box::new(LoadStack { offset: -2 })),
            LoadStack { offset: -2 },
            Eq,
            StoreRegister { reg: RR },
            Return
        ]
    }

    fn eq_int() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("eq$int"), Box::new(LoadStack { offset: -2 })),
            LoadStack { offset: -2 },
            Eq,
            StoreRegister { reg: RR },
            Return
        ]
    }

    fn eq_bool() -> Vec<Instruction> {
        vec![
            Labeled(Label::new("eq$bool"), Box::new(LoadStack { offset: -2 })),
            LoadStack { offset: -2 },
            Eq,
            StoreRegister { reg: RR },
            Return
        ]
    }

    fn lt_char() -> Vec<Instruction> {
        vec![]
    }

    fn lt_int() -> Vec<Instruction> {
        vec![]
    }

    fn gt_char() -> Vec<Instruction> {
        vec![]
    }

    fn gt_int() -> Vec<Instruction> {
        vec![]
    }

    fn le_char() -> Vec<Instruction> {
        vec![]
    }

    fn le_int() -> Vec<Instruction> {
        vec![]
    }

    fn ge_char() -> Vec<Instruction> {
        vec![]
    }

    fn ge_int() -> Vec<Instruction> {
        vec![]
    }
}

pub mod error {
    use std::error::Error;
    use std::fmt;
    use std::fmt::Debug;

    pub type Result<T, E = GenError> = std::result::Result<T, E>;

    #[derive(Clone)]
    pub enum GenError {
        MissingMain
    }

    impl fmt::Display for GenError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            match self {
                GenError::MissingMain => write!(f, "No main function found")
            }
        }
    }

    impl Debug for GenError {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "{}", self)
        }
    }

    impl Error for GenError {}
}
