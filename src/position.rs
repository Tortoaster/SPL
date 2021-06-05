use std::cmp::Ordering;
use std::fmt;
use std::fmt::Display;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

#[must_use]
#[derive(Clone, Debug, Eq, Ord)]
pub struct Pos<'a, T> {
    pub row: usize,
    pub col: usize,
    pub end_row: usize,
    pub end_col: usize,
    pub code: &'a str,
    pub content: T,
}

impl<'a, T: PartialEq> PartialEq for Pos<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.content == other.content
    }
}

impl<'a, T: PartialOrd> PartialOrd for Pos<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.content.partial_cmp(&other.content)
    }
}

impl<'a, T: Hash> Hash for Pos<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.content.hash(state)
    }
}

impl<'a, T: Display> fmt::Display for Pos<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "{} at {}:{}:", self.content, self.row + 1, self.col)?;
        let length = self.end_row - self.row + 1;
        let lines: Vec<&str> = self.code
            .lines()
            .take(self.end_row + 1)
            .skip(self.row)
            .collect();

        if self.row > 0 {
            writeln!(f, "| {}", self.code.lines().nth(self.row - 1).unwrap())?;
        }
        if length == 1 {
            let width = self.end_col - self.col + 1;
            writeln!(
                f,
                "| {}\n| {:>padding$}",
                lines[0],
                std::iter::repeat('^').take(width).collect::<String>(),
                padding = self.end_col
            )?;
        } else {
            let line = lines[0];
            let width = line.len() - self.col + 1;
            writeln!(
                f,
                "| {}\n| {:>padding$}",
                line,
                std::iter::repeat('^').take(width).collect::<String>(),
                padding = line.len()
            )?;
            for line in lines.iter().skip(1).take(length - 2) {
                writeln!(
                    f,
                    "| {}\n| {:>padding$}",
                    line,
                    std::iter::repeat('^').take(line.len()).collect::<String>(),
                    padding = 0
                )?;
            }
            let line = lines[length - 1];
            let width = self.end_col;
            writeln!(
                f,
                "| {}\n| {:>padding$}",
                line,
                std::iter::repeat('^').take(width).collect::<String>(),
                padding = 0
            )?;
        }
        if self.end_row + 1 < self.code.lines().count() {
            writeln!(f, "| {}", self.code.lines().nth(self.end_row + 1).unwrap())?;
        }

        Ok(())
    }
}

impl<'a, T> Pos<'a, T> {
    pub fn new(row: usize, col: usize, code: &'a str, content: T) -> Self {
        Pos {
            row,
            col,
            end_row: row,
            end_col: col,
            code,
            content,
        }
    }

    pub fn with<U>(&self, content: U) -> Pos<'a, U> {
        Pos {
            row: self.row,
            col: self.col,
            end_row: self.end_row,
            end_col: self.end_col,
            code: self.code,
            content,
        }
    }

    pub fn extend<U>(mut self, other: &Pos<U>) -> Self {
        if other.row < self.row {
            self.row = other.row;
            self.col = other.col;
        } else if other.row == self.row && other.col < self.col {
            self.col = other.col;
        };

        if other.end_row > self.end_row {
            self.end_row = other.end_row;
            self.end_col = other.end_col;
        } else if other.end_row == self.end_row && other.end_col > self.end_col {
            self.end_col = other.end_col;
        };

        self
    }

    pub fn grow(mut self, length: usize) -> Self {
        self.end_col += length;
        self
    }

    pub fn eject(self) -> (Pos<'a, ()>, T) {
        (self.with(()), self.content)
    }

    pub fn pos(&self) -> Pos<'a, ()> {
        self.with(())
    }
}

pub trait Join<'a> {
    fn join_with<'b, U>(&'b self, content: U) -> Option<Pos<'a, U>>;
}

impl<'a, T> Join<'a> for Vec<Pos<'a, T>> {
    fn join_with<'b, U>(&'b self, content: U) -> Option<Pos<'a, U>> {
        let mut iter = self.iter();
        let first = iter.next()?;
        let pos = iter.fold(first.with(()), |acc, pos|
            acc.extend(pos),
        );
        Some(pos.with(content))
    }
}

impl<'a, T> Deref for Pos<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.content
    }
}

impl<'a, T> DerefMut for Pos<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.content
    }
}
