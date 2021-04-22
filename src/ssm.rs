use std::fmt;

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

pub enum Instruction {
    LoadConstant(i32)
}

impl fmt::Display for Instruction {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Instruction::LoadConstant(c) => write!(f, "ldc {}", c)
        }
    }
}