use std::collections::HashMap;
use std::fmt;

use error::Result;

use crate::generator::error::GenError;
use crate::generator::prelude::*;
// Reserve scratch register to keep track of global variables
use crate::generator::Register::R7 as GP;
use crate::generator::Suffix;
use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, Id, PStmt, SPL, Stmt, VarDecl};
use crate::typer::Space;

const MAIN: &str = "main";

#[derive(Clone)]
struct Scope {
    global_values: HashMap<Id, Vec<Instruction>>,
    global_addresses: HashMap<Id, Vec<Instruction>>,
    local_values: HashMap<Id, Vec<Instruction>>,
    local_addresses: HashMap<Id, Vec<Instruction>>,
    arg_values: HashMap<Id, Vec<Instruction>>,
    arg_addresses: HashMap<Id, Vec<Instruction>>,
    function_args: HashMap<Id, Vec<Id>>,
    current_label: Label,
    ifs: usize,
    whiles: usize,
}

impl Scope {
    fn new(spl: &SPL) -> Self {
        Scope {
            global_values: HashMap::new(),
            global_addresses: HashMap::new(),
            local_values: HashMap::new(),
            local_addresses: HashMap::new(),
            arg_values: HashMap::new(),
            arg_addresses: HashMap::new(),
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
        instructions.append(&mut core::core().0);

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

impl Gen for Vec<PStmt<'_>> {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        Ok(self
            .iter()
            .map(|stmt| stmt.generate(scope))
            .collect::<Result<Vec<Vec<Instruction>>>>()?
            .into_iter()
            .flatten()
            .collect())
    }
}

impl Gen for Stmt<'_> {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let instructions = match self {
            Stmt::If(c, t, e) => {
                scope.ifs += 1;
                let else_label = scope.current_label
                    .clone()
                    .with_suffix(Suffix::Else(scope.ifs));
                let end_label = scope.current_label
                    .clone()
                    .with_suffix(Suffix::EndIf(scope.ifs));

                let mut instructions = c.generate(scope)?;
                if e.is_empty() {
                    instructions.push(BranchFalse { label: end_label.clone() });
                } else {
                    instructions.push(BranchFalse { label: else_label.clone() });
                }
                let mut then = t.generate(scope)?;
                instructions.append(&mut then);
                if !e.is_empty() {
                    instructions.push(Branch { label: end_label.clone() });
                    let mut otherwise = e.generate(scope)?;
                    let labeled = Labeled(else_label, Box::new(otherwise[0].clone()));
                    otherwise[0] = labeled;
                    instructions.append(&mut otherwise);
                }
                instructions.push(Labeled(end_label, Box::new(Nop)));
                instructions
            }
            Stmt::While(c, t) => {
                scope.whiles += 1;
                let start_label = scope.current_label
                    .clone()
                    .with_suffix(Suffix::While(scope.whiles));
                let end_label = scope.current_label
                    .clone()
                    .with_suffix(Suffix::EndWhile(scope.whiles));

                let mut instructions = c.generate(scope)?;
                let labeled = Labeled(start_label.clone(), Box::new(instructions[0].clone()));
                instructions[0] = labeled;
                instructions.push(BranchFalse { label: end_label.clone() });
                let mut t = t.generate(scope)?;
                t.push(Branch { label: start_label });
                t.push(Labeled(end_label, Box::new(Nop)));
                instructions.append(&mut t);
                instructions
            }
            Stmt::Assignment(id, fields, exp) => {
                // Generate value
                let mut instructions = exp.generate(scope)?;

                // Generate address
                instructions.append(&mut scope.push_address(id));
                for f in fields {
                    match f.inner {
                        Field::Head | Field::First => instructions.push(LoadAddress { offset: 0 }),
                        Field::Tail => instructions.push(LoadAddress { offset: -1 }),
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
                let mut instructions = r.generate(scope)?;
                instructions.append(&mut l.generate(scope)?);
                instructions.push(StoreMultiHeap { length: 2 });
                instructions
            }
        };

        Ok(instructions)
    }
}

impl Gen for FunCall<'_> {
    fn generate(&self, scope: &mut Scope) -> Result<Vec<Instruction>> {
        let arg_names = scope.function_args.get(&self.id);
        let instructions = match arg_names {
            // Builtin function
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
            // Custom function
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
        if !self.type_args.borrow().is_empty() {
            name.push_str(format!("{}", self.type_args
                .borrow()
                .iter()
                .map(|(_, t)| format!("-t{}", t))
                .collect::<Vec<String>>()
                .join("-a")
            ).as_str());
        }
        Label::new(name)
    }
}

mod core {
    use crate::generator::prelude::*;

    pub fn core() -> (Vec<Instruction>, Vec<Label>) {
        let mut instructions = Vec::new();
        let mut labels = Vec::new();

        let cores = vec![
            bin_op(vec![Label::new("eq-tInt"), Label::new("eq-tBool"), Label::new("eq-tChar")], Eq),
            bin_op(vec![Label::new("ne-tInt"), Label::new("ne-tBool"), Label::new("ne-tChar")], Ne),
            bin_op(vec![Label::new("lt-tInt"), Label::new("lt-tChar")], Lt),
            bin_op(vec![Label::new("gt-tInt"), Label::new("gt-tChar")], Gt),
            bin_op(vec![Label::new("le-tInt"), Label::new("le-tChar")], Le),
            bin_op(vec![Label::new("ge-tInt"), Label::new("ge-tChar")], Ge),
            bin_op(vec![Label::new("add")], Add),
            bin_op(vec![Label::new("add")], Add),
            bin_op(vec![Label::new("sub")], Sub),
            bin_op(vec![Label::new("mul")], Mul),
            bin_op(vec![Label::new("div")], Div),
            bin_op(vec![Label::new("mod")], Mod),
            bin_op(vec![Label::new("and")], And),
            bin_op(vec![Label::new("or")], Or),

            un_op(Label::new("neg"), Neg),
            un_op(Label::new("not"), Not),

            hd_basic(),
            tl_basic(),
            cons_basic(),
            is_empty_basic(),

            fst_basic(),
            snd_basic(),

            print_int(),
            print_bool(),
            print_char()
        ];

        for (i, l) in cores {
            instructions.push(i);
            labels.push(l);
        }

        (instructions.into_iter().flatten().collect(), labels.into_iter().flatten().collect())
    }

    fn un_op(label: Label, op: Instruction) -> (Vec<Instruction>, Vec<Label>) {
        (vec![
            Labeled(label.clone(), Box::new(LoadStack { offset: -1 })),
            op,
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn bin_op(labels: Vec<Label>, op: Instruction) -> (Vec<Instruction>, Vec<Label>) {
        (vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -2 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadStack { offset: -2 },
            op,
            StoreRegister { reg: RR },
            Return
        ], labels)
    }

    fn hd_basic() -> (Vec<Instruction>, Vec<Label>) {
        let labels = vec![
            Label::new("hd-tInt"),
            Label::new("hd-tBool"),
            Label::new("hd-tChar")
        ];
        let mut instructions = vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadStack { offset: 0 },
            BranchTrue { label: Label::new("hd-tInt--continue") },
        ];
        instructions.append(&mut Instruction::print_string("Error: head of empty list"));
        instructions.append(&mut vec![
            Halt,
            Labeled(Label::new("hd-tInt--continue"), Box::new(LoadHeap { offset: 0 })),
            StoreRegister { reg: RR },
            Return
        ]);

        (instructions, labels)
    }

    fn tl_basic() -> (Vec<Instruction>, Vec<Label>) {
        let labels = vec![
            Label::new("tl-tInt"),
            Label::new("tl-tBool"),
            Label::new("tl-tChar")
        ];
        let mut instructions = vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadStack { offset: 0 },
            BranchTrue { label: Label::new("tl-tInt--continue") },
        ];
        instructions.append(&mut Instruction::print_string("Error: tail of empty list"));
        instructions.append(&mut vec![
            Halt,
            Labeled(Label::new("tl-tInt--continue"), Box::new(LoadHeap { offset: -1 })),
            StoreRegister { reg: RR },
            Return
        ]);

        (instructions, labels)
    }

    fn cons_basic() -> (Vec<Instruction>, Vec<Label>) {
        let labels = vec![
            Label::new("cons-tInt"),
            Label::new("cons-tBool"),
            Label::new("cons-tChar")
        ];
        let instructions = vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadStack { offset: -3 },
            StoreMultiHeap { length: 2 },
            StoreRegister { reg: RR },
            Return
        ];
        (instructions, labels)
    }

    fn is_empty_basic() -> (Vec<Instruction>, Vec<Label>) {
        let labels = vec![
            Label::new("isEmpty-tInt"),
            Label::new("isEmpty-tBool"),
            Label::new("isEmpty-tChar")
        ];
        (vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadConstant(0),
            Eq,
            StoreRegister { reg: RR },
            Return
        ], labels)
    }

    fn fst_basic() -> (Vec<Instruction>, Vec<Label>) {
        let types = vec!["Int", "Bool", "Char"];
        let labels: Vec<Label> = types
            .iter()
            .flat_map(|a| types.iter().map(move |b| format!("fst-t{}-a-t{}", a, b)))
            .map(|s| Label::new(s))
            .collect();

        (vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadHeap { offset: 0 },
            StoreRegister { reg: RR },
            Return
        ], labels)
    }

    fn snd_basic() -> (Vec<Instruction>, Vec<Label>) {
        let types = vec!["Int", "Bool", "Char"];
        let labels: Vec<Label> = types
            .iter()
            .flat_map(|a| types.iter().map(move |b| format!("snd-t{}-a-t{}", a, b)))
            .map(|s| Label::new(s))
            .collect();

        (vec![
            labels
                .iter()
                .cloned()
                .fold(LoadStack { offset: -1 }, |instruction, label|
                    Labeled(label, Box::new(instruction)),
                ),
            LoadHeap { offset: -1 },
            StoreRegister { reg: RR },
            Return
        ], labels)
    }

    fn print_int() -> (Vec<Instruction>, Vec<Label>) {
        (vec![
            Labeled(Label::new("print-tInt"), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintInt },
            Return
        ], vec![Label::new("print-tInt")])
    }

    fn print_bool() -> (Vec<Instruction>, Vec<Label>) {
        let mut instructions = vec![
            Labeled(Label::new("print-tBool"), Box::new(LoadStack { offset: -1 })),
            BranchFalse { label: Label::new("print-tBool--else1") },
        ];
        instructions.append(&mut Instruction::print_string("True"));
        instructions.append(&mut vec![
            Branch { label: Label::new("print-tBool--endif1") },
            Labeled(Label::new("print-tBool--else1"), Box::new(Nop))
        ]);
        instructions.append(&mut Instruction::print_string("False"));
        instructions.push(Labeled(Label::new("print-tBool--endif1"), Box::new(Return)));

        (instructions, vec![Label::new("print-tBool")])
    }

    fn print_char() -> (Vec<Instruction>, Vec<Label>) {
        (vec![
            Labeled(Label::new("print-tChar"), Box::new(LoadStack { offset: -1 })),
            Trap { call: PrintChar },
            Return
        ], vec![Label::new("print-tChar")])
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
