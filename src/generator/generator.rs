use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::fmt;
use std::ops::Deref;

use error::Result;

use crate::generator::error::GenError;
use crate::generator::prelude::*;
// Reserve scratch register to keep track of global variables
use crate::generator::Register::R7 as GP;
use crate::generator::Suffix;
use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, Id, PStmt, SPL, Stmt, VarDecl};
use crate::position::Pos;
use crate::typer::{Space, Substitution};

const MAIN: &str = "main";

#[derive(Debug)]
struct Context<'a> {
    /// Function variants that still need to be generated
    needed: BTreeSet<FunCall<'a>>,
    /// Function variants that have been generated
    generated: HashSet<Label>,
}

impl Context<'_> {
    fn new() -> Self {
        Context {
            needed: BTreeSet::new(),
            generated: HashSet::new(),
        }
    }
}

#[derive(Clone, Debug)]
struct Scope<'a> {
    /// Get the value of a global variable
    global_values: HashMap<Id, Vec<Instruction>>,
    /// Get the address of a global variable
    global_addresses: HashMap<Id, Vec<Instruction>>,
    /// Get the value of a local variable
    local_values: HashMap<Id, Vec<Instruction>>,
    /// Get the address of a local variable
    local_addresses: HashMap<Id, Vec<Instruction>>,
    /// Get the names of the arguments of a function
    arg_names: HashMap<Id, Vec<Id>>,
    /// The call to the current function
    current_call: Option<FunCall<'a>>,
    /// Keeps track of the number of if statements in the current function
    ifs: usize,
    /// Keeps track of the number of while statements in the current function
    whiles: usize,
}

impl<'a> Scope<'a> {
    fn new(spl: &SPL<'a>) -> Self {
        Scope {
            global_values: HashMap::new(),
            global_addresses: HashMap::new(),
            local_values: HashMap::new(),
            local_addresses: HashMap::new(),
            arg_names: spl.decls
                .iter()
                .filter_map(|decl| match &decl.content {
                    Decl::VarDecl(_) => None,
                    Decl::FunDecl(fun_decl) => Some((fun_decl.id.content.clone(), fun_decl.args.iter().map(|id| id.content.clone()).collect()))
                })
                .collect(),
            current_call: None,
            ifs: 0,
            whiles: 0,
        }
    }

    fn clear_local(&mut self) {
        self.local_values.clear();
        self.local_addresses.clear();
        self.current_call = None;
        self.ifs = 0;
        self.whiles = 0;
    }

    fn push_address(&self, id: &Id) -> Vec<Instruction> {
        self.local_addresses
            .get(id)
            .cloned()
            .or_else(|| {
                let index = self.arg_names
                    .get(&self.current_call.as_ref().unwrap().id.content)?
                    .iter().position(|key| key == id);
                index.map(|index| vec![LoadLocalAddress { offset: -(index as isize) - 2 }])
            })
            .or(self.global_addresses.get(id).cloned())
            .unwrap()
            .clone()
    }

    fn push_var(&self, id: &Id) -> Vec<Instruction> {
        self.local_values
            .get(id)
            .cloned()
            .or_else(|| {
                let index = self.arg_names
                    .get(&self.current_call.as_ref()?.id.content)?
                    .iter().position(|key| key == id);
                index.map(|index| vec![LoadLocal { offset: -(index as isize) - 2 }])
            })
            .or(self.global_values.get(id).cloned())
            .expect(format!("Cannot find value {}", id).as_str())
            .clone()
    }
}

impl SPL<'_> {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program { instructions: self.generate(&mut Scope::new(self), &mut Context::new())? })
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

trait Gen<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>>;
}

impl<'a> Gen<'a> for SPL<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let (mut core_functions, core_labels) = core::core();
        context.generated.extend(core_labels);

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
            .map(|(index, decl)| match &decl.content {
                Decl::VarDecl(var_decl) => var_decl.generate_global(index as isize, scope, context),
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

        // Generate core functions
        instructions.append(&mut core_functions);

        // Generate code for main function
        let main_call = FunCall {
            id: Pos::new(
                1,
                1,
                " ",
                Id(MAIN.to_owned()),
            ),
            args: Vec::new(),
            type_args: RefCell::new(Substitution::new()),
        };
        context.needed.insert(main_call);

        // Keep generating necessary variants until all are done
        while !context.needed.is_empty() {
            let fun_call = context.needed.iter().next().unwrap().clone();
            let mut function = self.decls
                .iter()
                .find_map(|decl| match &decl.content {
                    Decl::FunDecl(fun_decl) => (fun_decl.id == fun_call.id).then(|| fun_decl),
                    _ => None
                })
                .ok_or(GenError::MissingMain)?
                .generate(&fun_call, scope, context)?;
            instructions.append(&mut function)
        }

        Ok(instructions)
    }
}

impl<'a> VarDecl<'a> {
    fn generate_global(&self, index: isize, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let offset = -index;

        // Initialization
        let mut instructions = self.exp.generate(scope, context)?;
        instructions.push(LoadRegister { reg: GP });
        instructions.push(StoreByAddress { offset });

        // Retrieving
        scope.global_values.insert(self.id.content.clone(), vec![
            LoadRegister { reg: GP },
            LoadAddress { offset }
        ]);
        scope.global_addresses.insert(self.id.content.clone(), vec![
            LoadRegister { reg: GP },
            ChangeAddress { offset }
        ]);

        Ok(instructions)
    }

    fn generate_local(&self, index: isize, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let offset = index + 1;
        // Initialization
        let mut instructions = self.exp.generate(scope, context)?;
        instructions.push(StoreLocal { offset });

        // Retrieving
        scope.local_values.insert(self.id.content.clone(), vec![LoadLocal { offset }]);
        scope.local_addresses.insert(self.id.content.clone(), vec![LoadLocalAddress { offset }]);

        Ok(instructions)
    }
}

impl<'a> FunDecl<'a> {
    fn generate(&self, fun_call: &FunCall<'a>, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let label = fun_call.label();
        context.needed.remove(fun_call);
        context.generated.insert(label.clone());

        let mut scope = scope.clone();
        scope.clear_local();
        scope.current_call = Some(fun_call.clone());

        let mut instructions = Vec::new();
        instructions.push(Labeled(label, Box::new(Link { length: self.var_decls.len() })));
        for (index, var) in self.var_decls.iter().enumerate() {
            let mut vars = var.generate_local(index as isize, &mut scope, context)?;
            instructions.append(&mut vars);
        }
        for stmt in &self.stmts {
            let mut stmts = stmt.generate(&mut scope, context)?;
            instructions.append(&mut stmts);
        }
        instructions.push(Unlink);
        instructions.push(Return);

        Ok(instructions)
    }
}

impl<'a> Gen<'a> for Vec<PStmt<'a>> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        Ok(self
            .iter()
            .map(|stmt| stmt.generate(scope, context))
            .collect::<Result<Vec<Vec<Instruction>>>>()?
            .into_iter()
            .flatten()
            .collect())
    }
}

impl<'a> Gen<'a> for Stmt<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let instructions = match self {
            Stmt::If(c, t, e) => {
                scope.ifs += 1;
                let label = scope.current_call.as_ref().unwrap().label();
                let else_label = label
                    .clone()
                    .with_suffix(Suffix::Else(scope.ifs));
                let end_label = label
                    .clone()
                    .with_suffix(Suffix::EndIf(scope.ifs));

                let mut instructions = c.generate(scope, context)?;
                if e.is_empty() {
                    instructions.push(BranchFalse { label: end_label.clone() });
                } else {
                    instructions.push(BranchFalse { label: else_label.clone() });
                }
                let mut then = t.generate(scope, context)?;
                instructions.append(&mut then);
                if !e.is_empty() {
                    instructions.push(Branch { label: end_label.clone() });
                    let mut otherwise = e.generate(scope, context)?;
                    let labeled = Labeled(else_label, Box::new(otherwise[0].clone()));
                    otherwise[0] = labeled;
                    instructions.append(&mut otherwise);
                }
                instructions.push(Labeled(end_label, Box::new(Nop)));
                instructions
            }
            Stmt::While(c, t) => {
                scope.whiles += 1;
                let label = scope.current_call.as_ref().unwrap().label();
                let start_label = label
                    .clone()
                    .with_suffix(Suffix::While(scope.whiles));
                let end_label = label
                    .clone()
                    .with_suffix(Suffix::EndWhile(scope.whiles));

                let mut instructions = c.generate(scope, context)?;
                let labeled = Labeled(start_label.clone(), Box::new(instructions[0].clone()));
                instructions[0] = labeled;
                instructions.push(BranchFalse { label: end_label.clone() });
                let mut t = t.generate(scope, context)?;
                t.push(Branch { label: start_label });
                t.push(Labeled(end_label, Box::new(Nop)));
                instructions.append(&mut t);
                instructions
            }
            Stmt::Assignment(id, fields, exp) => {
                // Generate value
                let mut instructions = exp.generate(scope, context)?;

                // Generate address
                instructions.append(&mut scope.push_address(id));
                for f in fields {
                    match f.content {
                        Field::Head | Field::First => instructions.push(LoadAddress { offset: 0 }),
                        Field::Tail => instructions.push(LoadAddress { offset: -1 }),
                        Field::Second => instructions.push(LoadAddress { offset: 1 })
                    }
                }

                // Store value at address
                instructions.push(StoreByAddress { offset: 0 });

                instructions
            }
            Stmt::FunCall(fun_call) => fun_call.generate(scope, context)?,
            Stmt::Return(ret) => {
                match ret {
                    None => vec![
                        Unlink,
                        Return
                    ],
                    Some(exp) => exp
                        .generate(scope, context)?
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
impl<'a> Gen<'a> for Exp<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let instructions = match self {
            Exp::Variable(id) => scope.push_var(id),
            Exp::Number(n) => vec![LoadConstant(*n)],
            Exp::Character(c) => vec![LoadConstant(*c as i32)],
            Exp::Boolean(b) => vec![LoadConstant(if *b { -1 } else { 0 })],
            Exp::FunCall(fun_call) => {
                let mut instructions = fun_call.generate(scope, context)?;
                instructions.push(LoadRegister { reg: RR });
                instructions
            }
            Exp::Nil => vec![LoadConstant(0)],
            Exp::Tuple(l, r) => {
                let mut instructions = r.generate(scope, context)?;
                instructions.append(&mut l.generate(scope, context)?);
                instructions.push(StoreMultiHeap { length: 2 });
                instructions
            }
        };

        Ok(instructions)
    }
}

impl<'a> Gen<'a> for FunCall<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let fun_call = {
            match scope.current_call.borrow().as_ref() {
                None => self.clone(),
                Some(current_call) => {
                    let subst = current_call.type_args.borrow();
                    let type_args = self.type_args.clone();
                    type_args.borrow_mut().apply(subst.deref());
                    let fun_call = FunCall {
                        id: self.id.clone(),
                        args: self.args.clone(),
                        type_args,
                    };
                    fun_call
                }
            }
        };
        let label = fun_call.label();
        if !context.generated.contains(&label) {
            context.needed.insert(fun_call.clone());
        }

        let instructions = fun_call.args
            .iter()
            .map(|arg| arg.generate(scope, context))
            .collect::<Result<Vec<Vec<Instruction>>>>()?
            .into_iter()
            .flatten()
            .chain(vec![
                // Branch to function
                BranchSubroutine { label },
                // Remove arguments
                AdjustStack { offset: -(fun_call.args.len() as isize) },
            ])
            .collect();

        Ok(instructions)
    }
}

impl FunCall<'_> {
    fn label(&self) -> Label {
        let mut name = format!("{}", self.id.content);
        if !self.type_args.borrow().is_empty() {
            name.push_str(format!("{}", self.type_args
                .borrow()
                .iter()
                .map(|(_, t)| format!("-t{}", t.content))
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
