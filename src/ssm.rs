use std::fmt;

pub mod prelude {
    pub use crate::ssm::Instruction::*;
    pub use crate::ssm::Register::*;
    pub use crate::ssm::Trap::*;
}

pub enum Register {
    PC,
    SP,
    MP,
    HP,
    RR,
    R0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
}

impl fmt::Display for Register {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Register::PC => write!(f, "PC"),
            Register::SP => write!(f, "SP"),
            Register::MP => write!(f, "MP"),
            Register::HP => write!(f, "HP"),
            Register::RR => write!(f, "RR"),
            Register::R0 => write!(f, "R0"),
            Register::R1 => write!(f, "R1"),
            Register::R2 => write!(f, "R2"),
            Register::R3 => write!(f, "R3"),
            Register::R4 => write!(f, "R4"),
            Register::R5 => write!(f, "R5"),
            Register::R6 => write!(f, "R6"),
            Register::R7 => write!(f, "R7")
        }
    }
}

pub struct Label(pub String);

impl Label {
    pub fn new(name: &str) -> Self {
        Label(name.to_owned())
    }
}

impl fmt::Display for Label {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

pub enum Instruction {
    // Stack instructions

    /// Pushes a value on the stack.
    LoadConstant(i32),

    /// Pushes item elsewhere on top.
    LoadStack { offset: isize },
    /// Pushes multiple items elsewhere on top.
    LoadMultiStack { offset: isize, length: usize },
    /// Moves topmost item elsewhere.
    StoreStack { offset: isize },
    /// Moves top n items elsewhere.
    StoreMultiStack { offset: isize, length: usize },
    /// Pushes address of item elsewhere.
    LoadStackAddress { offset: isize },

    // Local instructions

    /// Pushes item elsewhere on top.
    LoadLocal { offset: isize },
    /// Pushes multiple items elsewhere on top.
    LoadMultiLocal { offset: isize, length: usize },
    /// Moves topmost item elsewhere.
    StoreLocal { offset: isize },
    /// Moves top [`length`] items elsewhere.
    StoreMultiLocal { offset: isize, length: usize },
    /// Pushes address of item elsewhere.
    LoadLocalAddress { offset: isize },

    // Address instructions

    /// Loads value at address, pushed to stack.
    LoadAddress { address: usize },
    /// Loads multiple values at address, pushed to stack.
    LoadMultiAddress { address: usize, length: usize },
    // ldaa
    // sta
    // stma

    // Registers

    /// Pushes value from register on the stack.
    LoadRegister { register: Register },
    /// Copies a value from one register to the other.
    LoadRegisterFromRegister { to: Register, from: Register },
    /// Pops stack into [`register`].
    StoreRegister { register: Register },
    // swp
    // swpr
    // swprr

    // ???

    /// Adds offset to the SP.
    AdjustStack { offset: isize },

    // Operations

    Add,
    Mul,
    Sub,
    Div,
    Mod,
    And,
    Or,
    Xor,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    /// Negates top value on stack.
    Neg,
    /// Flips bits of top value on stack.
    Not,

    // Branching and subroutines

    BranchSubroutine { label: Label },
    /// Move to a label without remembering current address
    Branch { label: Label },
    // brf
    // brt
    /// Moves to the address on top of the stack.
    JumpSubroutine,
    /// Pops previous PC from the stack and jumps to it.
    Return,

    // Linking

    /// Reserves [`length`] spaces for local variables
    Link { length: usize },
    /// Removes local variables
    Unlink,

    // nop
    Halt,
    Trap { trap: Trap },
    // annote
    // ldh
    // ldmh
    // sth
    // stmh

    Labeled(Label, Box<Instruction>)
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::LoadConstant(constant) => write!(f, "ldc {}", constant),

            Instruction::LoadStack { offset } => write!(f, "lds {}", offset),
            Instruction::LoadMultiStack { offset, length } => write!(f, "ldms {} {}", offset, length),
            Instruction::StoreStack { offset } => write!(f, "sts {}", offset),
            Instruction::StoreMultiStack { offset, length } => write!(f, "stms {} {}", offset, length),
            Instruction::LoadStackAddress { offset } => write!(f, "ldsa {}", offset),

            Instruction::LoadLocal { offset } => write!(f, "ldl {}", offset),
            Instruction::LoadMultiLocal { offset, length } => write!(f, "ldml {} {}", offset, length),
            Instruction::StoreLocal { offset } => write!(f, "stl {}", offset),
            Instruction::StoreMultiLocal { offset, length } => write!(f, "stml {} {}", offset, length),
            Instruction::LoadLocalAddress { offset } => write!(f, "ldla {}", offset),

            Instruction::LoadRegister { register } => write!(f, "ldr {}", register),
            Instruction::LoadRegisterFromRegister { to, from } => write!(f, "ldrr {} {}", to, from),
            Instruction::StoreRegister { register } => write!(f, "str {}", register),

            Instruction::AdjustStack { offset } => write!(f, "ajs {}", offset),

            Instruction::Add => write!(f, "add"),
            Instruction::Mul => write!(f, "mul"),
            Instruction::Sub => write!(f, "sub"),
            Instruction::Div => write!(f, "div"),
            Instruction::Mod => write!(f, "mod"),
            Instruction::And => write!(f, "and"),
            Instruction::Or => write!(f, "or"),
            Instruction::Xor => write!(f, "xor"),
            Instruction::Eq => write!(f, "eq"),
            Instruction::Ne => write!(f, "ne"),
            Instruction::Lt => write!(f, "lt"),
            Instruction::Le => write!(f, "le"),
            Instruction::Gt => write!(f, "gt"),
            Instruction::Ge => write!(f, "ge"),
            Instruction::Neg => write!(f, "neg"),
            Instruction::Not => write!(f, "not"),

            Instruction::LoadAddress { address } => write!(f, "lda {}", address),
            Instruction::LoadMultiAddress { address, length } => write!(f, "ldma {} {}", address, length),

            Instruction::BranchSubroutine { label } => write!(f, "bsr {}", label),
            Instruction::Branch { label } => write!(f, "bra {}", label),
            Instruction::JumpSubroutine => write!(f, "jsr"),
            Instruction::Return => write!(f, "ret"),

            Instruction::Link { length } => write!(f, "link {}", length),
            Instruction::Unlink => write!(f, "unlink"),

            Instruction::Halt => write!(f, "halt"),
            Instruction::Trap { trap } => write!(f, "trap {}", trap),

            Instruction::Labeled(label, instruction) => write!(f, "{}: {}", label, instruction),
        }
    }
}

pub enum Trap {
    /// Pop a value from the stack and print it as an integer.
    PrintInt,
    /// Pop a value from the stack and print it as a character.
    PrintChar,
    /// Read an integer from stdin and push it on the stack.
    ReadInt,
    /// Read a character from stdin and push it on the stack.
    ReadChar,
    /// Read multiple characters from stdin and push them to the stack, null terminated.
    ReadString,
    /// Pop a filename from the stack and open it with read permission.
    OpenReadFile,
    /// Pop a filename from the stack and open it with write permission.
    OpenWriteFile,
    /// Pop a file pointer and read one character to push on the stack.
    ReadFromFile,
    /// Pop a character and a file pointer and write it to the file.
    WriteToFile,
    /// Pop a file pointer and close that file.
    CloseFile
}

impl fmt::Display for Trap {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Trap::PrintInt => write!(f, "0"),
            Trap::PrintChar => write!(f, "1"),
            Trap::ReadInt => write!(f, "10"),
            Trap::ReadChar => write!(f, "11"),
            Trap::ReadString => write!(f, "12"),
            Trap::OpenReadFile => write!(f, "20"),
            Trap::OpenWriteFile => write!(f, "21"),
            Trap::ReadFromFile => write!(f, "22"),
            Trap::WriteToFile => write!(f, "23"),
            Trap::CloseFile => write!(f, "24")
        }
    }
}
