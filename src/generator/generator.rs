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
use crate::lexer::Field;
use crate::parser::{Decl, Exp, FunCall, FunDecl, Id, PStmt, SPL, Stmt, VarDecl};
use crate::position::Pos;
use crate::typer::{Space, Substitution, Type};

const MAIN: &str = "main";

#[derive(Debug)]
pub struct Context<'a> {
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
pub struct Scope<'a> {
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
                    Decl::FunDecl(fun_decl) =>
                        Some((fun_decl.id.content.clone(), fun_decl.args
                            .iter()
                            .map(|id| id.content.clone())
                            .collect()))
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
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction>;
}

impl<'a> SPL<'a> {
    pub fn generate_code(&self) -> Result<Program> {
        Ok(Program {
            instructions: self.generate(&mut Scope::new(self), &mut Context::new())?
        })
    }

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
                Decl::VarDecl(var_decl) =>
                    var_decl.generate_global(index as isize, scope, context),
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
                0,
                0,
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
                    Decl::FunDecl(fun_decl) =>
                        (fun_decl.id == fun_call.id).then(|| fun_decl),
                    _ => None
                })
                .map(|a| a.generate(&fun_call, scope, context))
                .unwrap_or_else(|| match fun_call.id.content.0.as_str() {
                    "eq" => core::gen_eq(&fun_call).generate(&fun_call, scope, context),
                    "print" => vec![],
                    // "main" => return Err(GenError::MissingMain),
                    _ => panic!("cannot generate {}", fun_call.label())
                });
            instructions.append(&mut function)
        }

        Ok(instructions)
    }
}

impl<'a> VarDecl<'a> {
    fn generate_global(&self, index: isize, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Result<Vec<Instruction>> {
        let offset = -index;

        // Initialization
        let mut instructions = self.exp.generate(scope, context);
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

    fn generate_local(&self, index: isize, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
        let offset = index + 1;
        // Initialization
        let mut instructions = self.exp.generate(scope, context);
        instructions.push(StoreLocal { offset });

        // Retrieving
        scope.local_values.insert(self.id.content.clone(), vec![
            LoadLocal { offset }
        ]);
        scope.local_addresses.insert(self.id.content.clone(), vec![
            LoadLocalAddress { offset }
        ]);

        instructions
    }
}

impl<'a> FunDecl<'a> {
    fn generate(&self, fun_call: &FunCall<'a>, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
        let label = fun_call.label();
        context.needed.remove(fun_call);
        context.generated.insert(label.clone());

        let mut scope = scope.clone();
        scope.clear_local();
        scope.current_call = Some(fun_call.clone());

        let mut instructions = Vec::new();
        instructions.push(Labelled(label));
        instructions.push(Link { length: self.var_decls.len() });
        for (i, var) in self.var_decls.iter().enumerate() {
            let mut vars = var.generate_local(i as isize, &mut scope, context);
            instructions.append(&mut vars);
        }
        for stmt in &self.stmts {
            let mut stmts = stmt.generate(&mut scope, context);
            instructions.append(&mut stmts);
        }
        instructions.push(Unlink);
        instructions.push(Return);

        instructions
    }
}

impl<'a> Gen<'a> for Vec<PStmt<'a>> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
        self
            .iter()
            .flat_map(|stmt| stmt.generate(scope, context))
            .collect()
    }
}

impl<'a> Gen<'a> for Stmt<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
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

                let mut instructions = c.generate(scope, context);
                if e.is_empty() {
                    instructions.push(BranchFalse { label: end_label.clone() });
                } else {
                    instructions.push(BranchFalse { label: else_label.clone() });
                }
                let mut then = t.generate(scope, context);
                instructions.append(&mut then);
                if !e.is_empty() {
                    instructions.push(Branch { label: end_label.clone() });
                    let mut otherwise = e.generate(scope, context);
                    otherwise.insert(0, Labelled(else_label));
                    instructions.append(&mut otherwise);
                }
                instructions.push(Labelled(end_label));
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

                let mut instructions = c.generate(scope, context);
                let labeled = Labelled(start_label.clone());
                instructions.insert(0, labeled);
                instructions.push(BranchFalse { label: end_label.clone() });
                let mut t = t.generate(scope, context);
                t.push(Branch { label: start_label });
                t.push(Labelled(end_label));
                instructions.append(&mut t);
                instructions
            }
            Stmt::Assignment(id, fields, exp) => {
                // Generate value
                let mut instructions = exp.generate(scope, context);

                // Generate address
                instructions.append(&mut scope.push_address(id));
                for f in fields {
                    match f.content {
                        Field::Head |
                        Field::First => instructions.push(LoadAddress { offset: 0 }),
                        Field::Tail => instructions.push(LoadAddress { offset: -1 }),
                        Field::Second => instructions.push(LoadAddress { offset: 1 })
                    }
                }

                // Store value at address
                instructions.push(StoreByAddress { offset: 0 });

                instructions
            }
            Stmt::FunCall(fun_call) => fun_call.generate(scope, context),
            Stmt::Return(ret) => {
                match ret {
                    None => vec![
                        Unlink,
                        Return
                    ],
                    Some(exp) => exp
                        .generate(scope, context)
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

        instructions
    }
}

/// Generates an expression, leaving the result on top of the stack
impl<'a> Gen<'a> for Exp<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
        let instructions = match self {
            Exp::Variable(id) => scope.push_var(id),
            Exp::Number(n) => vec![LoadConstant(*n)],
            Exp::Character(c) => vec![LoadConstant(*c as i32)],
            Exp::Boolean(b) => vec![LoadConstant(if *b { -1 } else { 0 })],
            Exp::FunCall(fun_call) => {
                let mut instructions = fun_call.generate(scope, context);
                instructions.push(LoadRegister { reg: RR });
                instructions
            }
            Exp::Nil => vec![LoadConstant(0)],
            Exp::Tuple(l, r) => {
                let mut instructions = r.generate(scope, context);
                instructions.append(&mut l.generate(scope, context));
                instructions.push(StoreMultiHeap { length: 2 });
                instructions
            }
        };

        instructions
    }
}

impl<'a> Gen<'a> for FunCall<'a> {
    fn generate(&self, scope: &mut Scope<'a>, context: &mut Context<'a>) -> Vec<Instruction> {
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
            .flat_map(|arg| arg.generate(scope, context))
            .chain(vec![
                // Branch to function
                BranchSubroutine { label },
                // Remove arguments
                AdjustStack { offset: -(fun_call.args.len() as isize) },
            ])
            .collect();

        instructions
    }
}

impl FunCall<'_> {
    fn label(&self) -> Label {
        let mut name = format!("{}", self.id.content);
        if !self.type_args.borrow().is_empty() {
            name.push_str(format!("{}", self.type_args
                .borrow()
                .iter()
                .map(|(_, t)| format!("{}", t.label()))
                .collect::<Vec<String>>()
                .join("-a")
            ).as_str());
        }
        Label::new(name)
    }
}

impl Type<'_> {
    fn label(&self) -> String {
        match self {
            Type::Tuple(l, r) => format!("-P{}-c{}-p", l.label(), r.label()),
            Type::List(a) => format!("-L{}-l", a.label()),
            // Type::Function(_, _) => {},
            // Type::Polymorphic(_) => String::from("-x"),
            _ => format!("-t{}", self)
        }
    }
}

mod core {
    use std::cell::RefCell;
    use std::ops::Deref;

    use crate::generator::prelude::*;
    use crate::parser::{Exp, FunCall, FunDecl, Id, Stmt};
    use crate::typer::{Substitution, Type};

    pub fn gen_eq<'a>(fun_call: &FunCall<'a>) -> FunDecl<'a> {
        let t = fun_call.type_args.borrow().deref().values().next().unwrap().clone();
        match &t.content {
            Type::Tuple(l_type, r_type) => {
                let pos = fun_call.id.with(());
                let l1 = Exp::FunCall(FunCall {
                    id: pos.with(Id("fst".to_owned())),
                    args: vec![fun_call.args[0].clone()],
                    type_args: RefCell::new(Substitution::new())
                });
                let r1 = Exp::FunCall(FunCall {
                    id: pos.with(Id("snd".to_owned())),
                    args: vec![fun_call.args[0].clone()],
                    type_args: RefCell::new(Substitution::new())
                });
                let l2 = Exp::FunCall(FunCall {
                    id: pos.with(Id("fst".to_owned())),
                    args: vec![fun_call.args[1].clone()],
                    type_args: RefCell::new(Substitution::new())
                });
                let r2 = Exp::FunCall(FunCall {
                    id: pos.with(Id("snd".to_owned())),
                    args: vec![fun_call.args[1].clone()],
                    type_args: RefCell::new(Substitution::new())
                });
                let l_subst = fun_call.type_args
                    .borrow()
                    .iter()
                    .map(|(k, _)| (k.clone(), l_type.deref().clone()))
                    .collect();
                let l_fun_call = FunCall {
                    id: fun_call.id.clone(),
                    args: vec![pos.with(l1), pos.with(l2)],
                    type_args: RefCell::new(l_subst),
                };
                let r_subst = fun_call.type_args
                    .borrow()
                    .iter()
                    .map(|(k, _)| (k.clone(), r_type.deref().clone()))
                    .collect();
                let r_fun_call = FunCall {
                    id: fun_call.id.clone(),
                    args: vec![pos.with(r1), pos.with(r2)],
                    type_args: RefCell::new(r_subst),
                };
                let and = FunCall {
                    id: pos.with(Id("and".to_owned())),
                    args: vec![pos.with(Exp::FunCall(r_fun_call)), pos.with(Exp::FunCall(l_fun_call))],
                    type_args: RefCell::new(Substitution::new()),
                };
                let ret = Stmt::Return(Some(pos.with(Exp::FunCall(and))));
                FunDecl {
                    id: fun_call.id.clone(),
                    args: vec![pos.with(Id("left".to_owned())), pos.with(Id("right".to_owned()))],
                    fun_type: RefCell::new(pos.with(Some(pos.with(Type::Function(Box::new(t.clone()), Box::new(pos.with(Type::Function(Box::new(t), Box::new(pos.with(Type::Bool)))))))))),
                    var_decls: vec![],
                    stmts: vec![pos.with(ret)],
                }
            }
            Type::List(_) => unimplemented!(),
            _ => panic!()
        }
    }

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
            hd(),
            tl(),
            cons(),
            is_empty(),
            fst(),
            snd(),
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
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            op,
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn bin_op(labels: Vec<Label>, op: Instruction) -> (Vec<Instruction>, Vec<Label>) {
        (labels.iter().cloned().map(|l| Labelled(l)).chain(vec![
            LoadStack { offset: -2 },
            LoadStack { offset: -2 },
            op,
            StoreRegister { reg: RR },
            Return
        ]).collect(), labels)
    }

    fn hd() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("hd");
        let mut instructions = vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadStack { offset: 0 },
            BranchTrue { label: Label::new("hd--continue") },
        ];
        instructions.append(&mut Instruction::print_string("Error: head of empty list"));
        instructions.append(&mut vec![
            Halt,
            Labelled(Label::new("hd--continue")),
            LoadHeap { offset: 0 },
            StoreRegister { reg: RR },
            Return
        ]);

        (instructions, vec![label])
    }

    fn tl() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("tl");
        let mut instructions = vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadStack { offset: 0 },
            BranchTrue { label: Label::new("tl--continue") },
        ];
        instructions.append(&mut Instruction::print_string("Error: tail of empty list"));
        instructions.append(&mut vec![
            Halt,
            Labelled(Label::new("tl--continue")),
            LoadHeap { offset: -1 },
            StoreRegister { reg: RR },
            Return
        ]);

        (instructions, vec![label])
    }

    fn cons() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("cons");
        (vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadStack { offset: -3 },
            StoreMultiHeap { length: 2 },
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn is_empty() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("isEmpty");
        (vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadConstant(0),
            Eq,
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn fst() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("fst");
        (vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadHeap { offset: 0 },
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn snd() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("snd");
        (vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            LoadHeap { offset: -1 },
            StoreRegister { reg: RR },
            Return
        ], vec![label])
    }

    fn print_int() -> (Vec<Instruction>, Vec<Label>) {
        let label = Label::new("print-tInt");
        (vec![
            Labelled(label.clone()),
            LoadStack { offset: -1 },
            Trap { call: PrintInt },
            Return
        ], vec![Label::new("print-tInt")])
    }

    fn print_bool() -> (Vec<Instruction>, Vec<Label>) {
        let mut instructions = vec![
            Labelled(Label::new("print-tBool")),
            LoadStack { offset: -1 },
            BranchFalse { label: Label::new("print-tBool--else1") },
        ];
        instructions.append(&mut Instruction::print_string("True"));
        instructions.append(&mut vec![
            Branch { label: Label::new("print-tBool--endif1") },
            Labelled(Label::new("print-tBool--else1"))
        ]);
        instructions.append(&mut Instruction::print_string("False"));
        instructions.push(Labelled(Label::new("print-tBool--endif1")));
        instructions.push(Return);

        (instructions, vec![Label::new("print-tBool")])
    }

    fn print_char() -> (Vec<Instruction>, Vec<Label>) {
        (vec![
            Labelled(Label::new("print-tChar")),
            LoadStack { offset: -1 },
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
