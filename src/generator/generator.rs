use std::collections::HashMap;
use std::fmt;

use error::Result;

use crate::generator::error::GenError;
use crate::generator::prelude::*;
// Reserve first scratch register to keep track of global variables
use crate::generator::Register::R7 as GP;
use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, Id, SPL, Stmt, VarDecl};
use crate::typer::Space;

const MAIN: &str = "main";

#[derive(Clone)]
struct Scope<'a> {
    global_values: HashMap<Id, Vec<Instruction>>,
    global_addresses: HashMap<Id, Vec<Instruction>>,
    local_values: HashMap<Id, Vec<Instruction>>,
    local_addresses: HashMap<Id, Vec<Instruction>>,
    arg_values: HashMap<Id, Vec<Instruction>>,
    arg_addresses: HashMap<Id, Vec<Instruction>>,
    functions: HashMap<FunCall<'a>, Vec<Instruction>>,
    function_args: HashMap<Id, Vec<Id>>,
    current_label: Label,
    ifs: usize,
    whiles: usize,
}

impl Scope<'_> {
    fn new(spl: &SPL) -> Self {
        Scope {
            global_values: HashMap::new(),
            global_addresses: HashMap::new(),
            local_values: HashMap::new(),
            local_addresses: HashMap::new(),
            arg_values: HashMap::new(),
            arg_addresses: HashMap::new(),
            functions: HashMap::new(),
            current_label: Label::new(MAIN),
            function_args: spl.decls
                .iter()
                .filter_map(|decl| match &decl.inner {
                    Decl::VarDecl(_) => None,
                    Decl::FunDecl(fun_decl) => Some((fun_decl.id.inner.clone(), fun_decl.args.iter().map(|id| id.inner.clone()).collect()))
                })
                .collect(),
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

impl SPL<'_> {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate(&mut Scope::new(self))? })
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

impl Gen for SPL<'_> {
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
            .map(|(index, decl)| match &decl.inner {
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
            .find_map(|decl| match &decl.inner {
                Decl::FunDecl(fun_decl) => (fun_decl.id.inner == Id(MAIN.to_owned())).then(|| fun_decl),
                _ => None
            })
            .ok_or(GenError::MissingMain)?
            .generate(Label::new(MAIN), scope)?;
        instructions.append(&mut functions);

        // Keep generating necessary variants until all are done

        // Generate core functions
        instructions.append(&mut core::core());

        Ok(instructions)
    }
}

impl VarDecl<'_> {
    fn generate_global(&self, index: isize, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let offset = -index;

        // Initialization
        let mut instructions = self.exp.generate(scope)?;
        instructions.push(LoadRegister { reg: GP });
        instructions.push(StoreByAddress { offset });

        // Retrieving
        scope.global_values.insert(self.id.inner.clone(), vec![
            LoadRegister { reg: GP },
            LoadAddress { offset }
        ]);
        scope.global_addresses.insert(self.id.inner.clone(), vec![
            LoadRegister { reg: GP },
            ChangeAddress { offset }
        ]);

        Ok(instructions)
    }

    fn generate_local(&self, index: isize, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let offset = index + 1;
        // Initialization
        let mut instructions = self.exp.generate(scope)?;
        instructions.push(StoreLocal { offset });

        // Retrieving
        scope.local_values.insert(self.id.inner.clone(), vec![LoadLocal { offset }]);
        scope.local_addresses.insert(self.id.inner.clone(), vec![LoadLocalAddress { offset }]);

        Ok(instructions)
    }

    fn generate_arg(id: Id, arg: &Exp, index: isize, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let offset = -index - 2;
        let instructions = arg.generate(scope)?;

        scope.arg_values.insert(id.clone(), vec![LoadLocal { offset }]);
        scope.arg_addresses.insert(id, vec![LoadLocalAddress { offset }]);

        Ok(instructions)
    }
}

impl FunDecl<'_> {
    fn generate(&self, label: Label, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let mut instructions = Vec::new();
        let scope = &mut scope.clone();
        scope.clear_local();
        scope.current_label = label;

        instructions.push(Labeled(Label::new(&self.id.inner.to_string()), Box::new(Link { length: self.var_decls.len() })));
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

impl Gen for Stmt<'_> {
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
                    match f.inner {
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
            Stmt::FunCall(fun_call) => fun_call.generate(scope)?,
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
impl Gen for Exp<'_> {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let instructions = match self {
            Exp::Variable(id) => scope.push_var(id),
            Exp::Number(n) => vec![LoadConstant(*n)],
            Exp::Character(c) => vec![LoadConstant(*c as i32)],
            Exp::Boolean(b) => vec![LoadConstant(if *b { -1 } else { 0 })],
            Exp::FunCall(fun_call) => {
                let mut instructions = fun_call.generate(scope)?;
                instructions.push(LoadRegister { reg: RR });
                instructions
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

impl Gen for FunCall<'_> {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let arg_names = scope.function_args.get(&self.id);
        let instructions = match arg_names {
            None => self.args
                .iter()
                .map(|arg| arg.generate(scope))
                .collect::<Result<Vec<Vec<Instruction>>>>()?
                .into_iter()
                .flatten()
                .chain(vec![
                    // Branch to function
                    BranchSubroutine { label: self.label() },
                    // Remove arguments
                    AdjustStack { offset: -(self.args.len() as isize) },
                ])
                .collect(),
            Some(names) => self.args
                .iter()
                .zip(names.clone())
                .enumerate()
                .map(|(index, (arg, id))| VarDecl::generate_arg(id, arg, index as isize, scope))
                .collect::<Result<Vec<Vec<Instruction>>>>()?
                .into_iter()
                .flatten()
                .chain(vec![
                    // Branch to function
                    BranchSubroutine { label: self.label() },
                    // Remove arguments
                    AdjustStack { offset: -(self.args.len() as isize) },
                ])
                .collect()
        };

        Ok(instructions)
    }
}

impl FunCall<'_> {
    fn label(&self) -> Label {
        let mut name = format!("{}", self.id.inner);
        if !self.type_args.is_empty() {
            name.push_str(format!("-t{}", self.type_args
                .iter()
                .map(|(_, t)| format!("{}", t))
                .collect::<Vec<String>>()
                .join("-a")
            ).as_str());
        }
        Label::new(name)
    }
}

mod core {
    use crate::generator::prelude::*;
    use crate::typer::Type;

    pub fn core() -> Vec<Instruction> {
        std::iter::empty()
            .chain(print_int())
            .chain(print_bool())
            .chain(print_char())
            .chain(bin_op(Label::new("add"), Add))
            .chain(bin_op(Label::new("sub"), Sub))
            .chain(bin_op(Label::new("mul"), Mul))
            .chain(bin_op(Label::new("div"), Div))
            .chain(bin_op(Label::new("mod"), Mod))
            .chain(un_op(Label::new("neg"), Neg))
            .chain(bin_op(Label::new("and"), And))
            .chain(bin_op(Label::new("or"), Or))
            .chain(un_op(Label::new("not"), Not))
            .collect()
    }

    fn un_op(label: Label, op: Instruction) -> Vec<Instruction> {
        vec![
            Labeled(label, Box::new(LoadStack { offset: -1 })),
            op,
            StoreRegister { reg: RR },
            Return
        ]
    }

    fn bin_op(label: Label, op: Instruction) -> Vec<Instruction> {
        vec![
            Labeled(label, Box::new(LoadStack { offset: -2 })),
            LoadStack { offset: -2 },
            op,
            StoreRegister { reg: RR },
            Return
        ]
    }

    fn print_char() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print-t{}", Type::Char)), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintChar },
            Return
        ]
    }

    fn print_int() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print-t{}", Type::Int)), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintInt },
            Return
        ]
    }

    fn print_bool() -> Vec<Instruction> {
        vec![
            Labeled(Label::new(format!("print-t{}", Type::Bool)), Box::new(LoadStack { offset: -1 })),
            BranchFalse { label: Label::new(format!("print-t{}--else1", Type::Bool)) },
            LoadConstant('T' as i32),
            Trap { call: PrintChar },
            LoadConstant('r' as i32),
            Trap { call: PrintChar },
            LoadConstant('u' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Branch { label: Label::new(format!("print-t{}--endif1", Type::Bool)) },
            Labeled(Label::new(format!("print-t{}--else1", Type::Bool)), Box::new(LoadConstant('F' as i32))),
            Trap { call: PrintChar },
            LoadConstant('a' as i32),
            Trap { call: PrintChar },
            LoadConstant('l' as i32),
            Trap { call: PrintChar },
            LoadConstant('s' as i32),
            Trap { call: PrintChar },
            LoadConstant('e' as i32),
            Trap { call: PrintChar },
            Labeled(Label::new(format!("print-t{}--endif1", Type::Bool)), Box::new(Return)),
        ]
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
