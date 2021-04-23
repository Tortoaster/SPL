use std::fmt;

pub mod prelude {
    pub use super::Instruction::*;
    pub use super::Register::*;
    pub use super::Color::*;
    pub use super::Trap::*;
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

pub struct Label(String);

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
    /// Adds an offset to the address on top of the stack.
    ChangeAddress { offset: isize },
    /// Pops an address and a value, then stores that value on the address offset by [`offset`].
    StoreByAddress { offset: isize },
    /// Pops an address and [`length`] values, then stores those values on the address offset by [`offset`].
    StoreMultiByAddress { offset: isize, length: usize },

    // Registers

    /// Pushes value from reg on the stack.
    LoadRegister { reg: Register },
    /// Copies a value from one reg to the other.
    LoadRegisterFromRegister { to: Register, from: Register },
    /// Pops stack into [`reg`].
    StoreRegister { reg: Register },

    // Swapping

    /// Swaps the top two values on the stack.
    Swap,
    /// Swaps the top value on the stack with the value in [`reg`].
    SwapRegister { reg: Register },
    /// Swaps the values of two regs.
    SwapRegisters { reg1: Register, reg2: Register },

    // Adjust stack

    /// Adds offset to the SP.
    AdjustStack { offset: isize },

    // Operations

    /// Adds top two stack values, pushes the result.
    Add,
    /// Multiplies top two stack values, pushes the result.
    Mul,
    /// Subtracts top stack value from the value after it, pushes the result.
    Sub,
    /// Divides top two stack values (top value being the divider), pushes the result.
    Div,
    /// Modulo of top two stack values (top value being the modulus), pushes the result.
    Mod,
    /// Performs and operation on the top two values on the stack, pushes the result.
    And,
    /// Performs or operation on the top two values on the stack, pushes the result.
    Or,
    /// Performs exclusive-or operation on the top two values on the stack, pushes the result.
    Xor,
    /// Performs equals operation on the top two values on the stack, pushes the result.
    Eq,
    /// Performs unequals operation on the top two values on the stack, pushes the result.
    Ne,
    /// Performs less-than operation on the top two values on the stack, pushes the result.
    Lt,
    /// Performs less-equals operation on the top two values on the stack, pushes the result.
    Le,
    /// Performs greater-than operation on the top two values on the stack, pushes the result.
    Gt,
    /// Performs greater-equal operation on the top two values on the stack, pushes the result.
    Ge,
    /// Negates top value on stack.
    Neg,
    /// Flips bits of top value on stack.
    Not,

    // Branching and subroutines

    /// Move to a label, remembering the current address.
    BranchSubroutine { label: Label },
    /// Move to a label without remembering the current address.
    Branch { label: Label },
    /// Pops a boolean of the stack, jumps to [`label`] if it's false.
    BranchFalse { label: Label },
    /// Pops a boolean of the stack, jumps to [`label`] if it's true.
    BranchTrue { label: Label },
    /// Moves to the address on top of the stack.
    JumpSubroutine,
    /// Pops remembered address from the stack and jumps to it.
    Return,

    // Linking

    /// Reserves [`length`] spaces for local variables.
    Link { length: usize },
    /// Removes local variables.
    Unlink,

    // Miscellaneous

    /// Does nothing.
    Nop,
    /// Stops the program.
    Halt,
    /// Used for input and output, behavior depends on the [`trap`].
    Trap { trap: Trap },
    /// Annotates the values from the address in [`reg`] offset by [`from`],
    /// until the same address offset by [`to`].
    Annotate { reg: Register, from: isize, to: isize, color: Color, desc: String },

    // Heap

    /// Pushes heap value on the stack.
    LoadHeap { offset: isize },
    /// Pushes multiple heap values on the stack.
    LoadMultiHeap { offset: isize, length: usize },
    /// Pops a value from the stack and stores it on the heap, pushes the address.
    StoreHeap { offset: isize },
    /// Pops [`length`] values from the stack and stores them on the heap, pushes the last address.
    StoreMultiHeap { offset: isize, length: usize },

    // Labels

    /// Adds a label to an instruction.
    Labeled(Label, Box<Instruction>),
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

            Instruction::LoadAddress { address } => write!(f, "lda {}", address),
            Instruction::LoadMultiAddress { address, length } => write!(f, "ldma {} {}", address, length),
            Instruction::ChangeAddress { offset } => write!(f, "ldaa {}", offset),
            Instruction::StoreByAddress { offset } => write!(f, "sta {}", offset),
            Instruction::StoreMultiByAddress { offset, length } => write!(f, "stma {} {}", offset, length),

            Instruction::LoadRegister { reg } => write!(f, "ldr {}", reg),
            Instruction::LoadRegisterFromRegister { to, from } => write!(f, "ldrr {} {}", to, from),
            Instruction::StoreRegister { reg } => write!(f, "str {}", reg),

            Instruction::Swap => write!(f, "swp"),
            Instruction::SwapRegister { reg } => write!(f, "swpr {}", reg),
            Instruction::SwapRegisters { reg1, reg2 } => write!(f, "swprr {} {}", reg1, reg2),

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

            Instruction::BranchSubroutine { label } => write!(f, "bsr {}", label),
            Instruction::Branch { label } => write!(f, "bra {}", label),
            Instruction::BranchFalse { label } => write!(f, "brf {}", label),
            Instruction::BranchTrue { label } => write!(f, "brt {}", label),
            Instruction::JumpSubroutine => write!(f, "jsr"),
            Instruction::Return => write!(f, "ret"),

            Instruction::Link { length } => write!(f, "link {}", length),
            Instruction::Unlink => write!(f, "unlink"),

            Instruction::Nop => write!(f, "nop"),
            Instruction::Halt => write!(f, "halt"),
            Instruction::Trap { trap } => write!(f, "trap {}", trap),
            Instruction::Annotate { reg, from, to, color, desc } =>
                write!(f, "annote {} {} {} {} {}", reg, from, to, color, desc),

            Instruction::LoadHeap { offset } => write!(f, "ldh, {}", offset),
            Instruction::LoadMultiHeap { offset, length } => write!(f, "ldmh, {} {}", offset, length),
            Instruction::StoreHeap { offset } => write!(f, "sth, {}", offset),
            Instruction::StoreMultiHeap { offset, length } => write!(f, "stmh, {} {}", offset, length),

            Instruction::Labeled(label, instruction) => write!(f, "{}: {}", label, instruction)
        }
    }
}

pub enum Color {
    Black,
    Blue,
    Cyan,
    DarkGray,
    Gray,
    Green,
    LightGray,
    Magenta,
    Orange,
    Pink,
    Red,
    Yellow,
}

impl fmt::Display for Color {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Color::Black => write!(f, "black"),
            Color::Blue => write!(f, "blue"),
            Color::Cyan => write!(f, "cyan"),
            Color::DarkGray => write!(f, "darkGray"),
            Color::Gray => write!(f, "gray"),
            Color::Green => write!(f, "green"),
            Color::LightGray => write!(f, "lightGray"),
            Color::Magenta => write!(f, "magenta"),
            Color::Orange => write!(f, "orange"),
            Color::Pink => write!(f, "pink"),
            Color::Red => write!(f, "red"),
            Color::Yellow => write!(f, "yellow")
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
    CloseFile,
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
