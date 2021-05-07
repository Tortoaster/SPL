use std::collections::{HashMap, HashSet};
use std::fmt;

use error::Result;

use crate::algorithm_w::{Space, Type};
use crate::generator::error::GenError;
use crate::lexer::Field;
use crate::ssm::prelude::*;
// Reserve first scratch register to keep track of global variables
use crate::ssm::Register::R0 as GP;
use crate::tree::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
use crate::typer::DecoratedSPL;

const MAIN: &str = "main";

#[derive(Clone)]
struct Scope {
    global_values: HashMap<Id, Vec<Instruction>>,
    global_addresses: HashMap<Id, Vec<Instruction>>,
    local_values: HashMap<Id, Vec<Instruction>>,
    local_addresses: HashMap<Id, Vec<Instruction>>,
    arg_values: HashMap<Id, Vec<Instruction>>,
    arg_addresses: HashMap<Id, Vec<Instruction>>,
    functions: HashMap<FunCall, Vec<Instruction>>,
    current_label: Label,
    ifs: usize,
    whiles: usize,
}

impl Scope {
    fn new() -> Self {
        Scope {
            global_values: HashMap::new(),
            global_addresses: HashMap::new(),
            local_values: HashMap::new(),
            local_addresses: HashMap::new(),
            arg_values: HashMap::new(),
            arg_addresses: HashMap::new(),
            functions: HashMap::new(),
            current_label: Label::new(""),
            ifs: 0,
            whiles: 0,
        }
    }

    fn clear_local(&mut self) {
        self.local_values.clear();
        self.arg_values.clear();
        self.ifs = 0;
        self.whiles = 0;
    }

    fn push_address(&self, id: &Id) -> Vec<Instruction> {
        self.local_addresses
            .get(id)
            .or(self.arg_addresses.get(id))
            .or(self.global_addresses.get(id))
            .unwrap()
            .clone()
    }

    fn push_var(&self, id: &Id) -> Vec<Instruction> {
        self.local_values
            .get(id)
            .or(self.arg_values.get(id))
            .or(self.global_values.get(id))
            .unwrap()
            .clone()
    }
}

impl DecoratedSPL {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate(&mut Scope::new())? })
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
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>>;
}

impl Gen for SPL {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
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
        let mut variables = self.decls
            .iter()
            .enumerate()
            .map(|(index, decl)| match decl {
                Decl::VarDecl(var_decl) => var_decl.generate_global(index as isize, scope),
                _ => Ok(Vec::new())
            })
            .collect::<Result<Vec<Vec<Instruction>>>>()?
            .into_iter()
            .flatten()
            .collect();
        instructions.append(&mut variables);

        // Move to main function, halt when it returns
        instructions.push(BranchSubroutine { label: Label::new(MAIN) });
        instructions.push(Halt);

        // Generate code for main function
        let mut functions = self.decls
            .iter()
            .find_map(|decl| match decl {
                Decl::FunDecl(fun_decl) => (fun_decl.id == Id(MAIN.to_owned())).then(|| fun_decl),
                _ => None
            })
            .ok_or(GenError::MissingMain)?
            .generate(scope)?;
        instructions.append(&mut functions);

        // Keep generating necessary variants until all are done

        // Generate core functions
        instructions.append(&mut core::core());

        Ok(instructions)
    }
}

impl VarDecl {
    fn generate_global(&self, index: isize, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let offset = -index - 1;

        // Initialization
        let mut instructions = self.exp.generate(scope)?;
        instructions.push(LoadRegister { reg: GP });
        instructions.push(StoreByAddress { offset });

        // Retrieving
        scope.global_values.insert(self.id.clone(), vec![
            LoadRegister { reg: GP },
            LoadAddress { offset }
        ]);
        scope.global_addresses.insert(self.id.clone(), vec![
            LoadRegister { reg: GP },
            ChangeAddress { offset }
        ]);

        Ok(instructions)
    }

    fn generate_local(&self, index: isize, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let offset = index + 1;
        // Initialization
        let instructions = self.exp.generate(scope)?;

        // Retrieving
        scope.local_values.insert(self.id.clone(), vec![LoadLocal { offset }]);
        scope.local_addresses.insert(self.id.clone(), vec![LoadLocalAddress { offset }]);

        Ok(instructions)
    }
}

impl Gen for FunDecl {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let mut instructions = Vec::new();
        let scope = &mut scope.clone();
        scope.clear_local();

        instructions.push(Labeled(Label::new(&self.id.to_string()), Box::new(Link { length: self.var_decls.len() })));
        for (index, var) in self.var_decls.iter().enumerate() {
            let mut vars = var.generate_local(index as isize, scope)?;
            instructions.append(&mut vars);
        }
        for stmt in &self.stmts {
            let mut stmts = stmt.generate(scope)?;
            instructions.append(&mut stmts);
        }
        instructions.push(Unlink);
        instructions.push(Return);

        Ok(instructions)
    }
}

impl Gen for Stmt {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let instructions = match self {
            Stmt::If(c, t, e) => {
                scope.ifs += 1;
                let else_label = scope.current_label
                    .clone()
                    .with_suffix(format!("else{}", scope.ifs));
                let end_label = scope.current_label
                    .clone()
                    .with_suffix(format!("endif{}", scope.ifs));

                let mut c = c.generate(scope)?;
                c.push(BranchFalse { label: else_label.clone() });
                let mut t: Vec<Instruction> = t
                    .iter()
                    .map(|stmt| stmt.generate(scope))
                    .collect::<Result<Vec<Vec<Instruction>>>>()?
                    .into_iter()
                    .flatten()
                    .collect();
                t.push(Branch { label: end_label.clone() });
                let mut e: Vec<Instruction> = e
                    .iter()
                    .map(|stmt| stmt.generate(scope))
                    .collect::<Result<Vec<Vec<Instruction>>>>()?
                    .into_iter()
                    .flatten()
                    .collect();
                let labeled = Labeled(else_label, Box::new(e[0].clone()));
                e[0] = labeled;
                e.push(Labeled(end_label, Box::new(Nop)));
                c.append(&mut t);
                c.append(&mut e);
                c
            }
            Stmt::While(c, t) => {
                scope.whiles += 1;
                let start_label = scope.current_label
                    .clone()
                    .with_suffix(format!("while{}", scope.ifs));
                let end_label = scope.current_label
                    .clone()
                    .with_suffix(format!("endwhile{}", scope.ifs));

                let mut c = c.generate(scope)?;
                let labeled = Labeled(start_label.clone(), Box::new(c[0].clone()));
                c[0] = labeled;
                c.push(BranchFalse { label: end_label.clone() });
                let mut t: Vec<Instruction> = t
                    .iter()
                    .map(|stmt| stmt.generate(scope))
                    .collect::<Result<Vec<Vec<Instruction>>>>()?
                    .into_iter()
                    .flatten()
                    .collect();
                t.push(Branch { label: start_label });
                t.push(Labeled(end_label, Box::new(Nop)));
                c.append(&mut t);
                c
            }
            Stmt::Assignment(id, fields, exp) => {
                // Generate value
                let mut instructions = exp.generate(scope)?;

                // Generate address
                instructions.append(&mut scope.push_address(id));
                for f in fields {
                    match f {
                        Field::Head | Field::First => instructions.push(LoadAddress { offset: 0 }),
                        Field::Tail => instructions.append(&mut vec![
                            LoadAddress { offset: 1 },
                            LoadAddress { offset: 0 },
                        ]),
                        Field::Second => instructions.push(LoadAddress { offset: 1 })
                    }
                }

                // Store value at address
                instructions.push(StoreByAddress { offset: 0 });

                instructions
            }
            Stmt::FunCall(fun_call) => fun_call.args
                .iter()
                .map(|arg| arg.generate(scope))
                .collect::<Result<Vec<Vec<Instruction>>>>()?
                .into_iter()
                .flatten()
                .chain(vec![
                    // Branch to function
                    BranchSubroutine { label: fun_call.label() },
                    // Remove arguments
                    AdjustStack { offset: -(fun_call.args.len() as isize) },
                ])
                .collect(),
            Stmt::Return(ret) => {
                match ret {
                    None => vec![
                        Unlink,
                        Return
                    ],
                    Some(exp) => exp
                        .generate(scope)?
                        .into_iter()
                        .chain(vec![
                            StoreRegister { reg: RR },
                            Unlink,
                            Return
                        ])
                        .collect()
                }
            }
        };

        Ok(instructions)
    }
}

/// Generates an expression, leaving the result on top of the stack
impl Gen for Exp {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
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
                    .collect::<Result<Vec<Vec<Instruction>>>>()?
                    .into_iter()
                    .flatten()
                    .chain(vec![
                        // Branch to function
                        BranchSubroutine { label: fun_call.label() },
                        // Remove arguments
                        AdjustStack { offset: -(fun_call.args.len() as isize) },
                        // Push result
                        LoadRegister { reg: RR }
                    ])
                    .collect()
            }
            Exp::Nil => vec![LoadConstant(0)],
            Exp::Tuple(l, r) => {
                let mut x = l.generate(scope)?;
                x.push(StoreHeap { offset: 0 });
                let mut y = r.generate(scope)?;
                y.push(StoreHeap { offset: 0 });
                y.push(AdjustStack { offset: -1 });
                x.append(&mut y);
                x
            }
        };

        Ok(instructions)
    }
}

impl FunCall {
    fn label(&self) -> Label {
        Label::new(format!("{}", self))
    }
}

impl fmt::Display for FunCall {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.id)?;
        if !self.type_args.is_empty() {
            write!(f, "${}", self.type_args
                .iter()
                .map(|(_, t)| format!("{}", t))
                .collect::<Vec<String>>()
                .join("&"))?;
        }
        Ok(())
    }
}

mod core {
    use crate::algorithm_w::Type;
    use crate::ssm::prelude::*;

    pub fn core() -> Vec<Instruction> {
        std::iter::empty()
            .chain(print_int())
            .chain(print_bool())
            .chain(print_char())
            .collect()
    }

    fn print_char() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print${}", Type::Char)), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintChar },
            Return
        ]
    }

    fn print_int() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print${}", Type::Int)), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintInt },
            Return
        ]
    }

    fn print_bool() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print${}", Type::Bool)), Box::new(LoadStack { offset: -1 })),
            BranchFalse { label: Label::new(format!("print${}-else1", Type::Bool)) },
            LoadConstant('T' as i32),
            Trap { call: PrintChar },
            LoadConstant('r' as i32),
            Trap { call: PrintChar },
            LoadConstant('u' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Branch { label: Label::new(format!("print${}-endif1", Type::Bool)) },
            Labeled(Label::new(format!("print${}-else1", Type::Bool)), Box::new(LoadConstant('F' as i32))),
            Trap { call: PrintChar },
            LoadConstant('a' as i32),
            Trap { call: PrintChar },
            LoadConstant('l' as i32),
            Trap { call: PrintChar },
            LoadConstant('s' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Labeled(Label::new(format!("print${}-endif1", Type::Bool)), Box::new(Return)),
        ]
    }

    // fn op(label: Label, op: Instruction) -> Vec<Instruction> {
    //     vec![
    //         Labeled(label, Box::new(LoadStack { offset: -2 })),
    //         LoadStack { offset: -2 },
    //         op,
    //         StoreRegister { reg: RR },
    //         Return
    //     ]
    // }

    // hd, tl, cons, fst, snd, isEmpty
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
