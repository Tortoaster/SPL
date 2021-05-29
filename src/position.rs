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
        write!(f, "{}", self.content)?;
        writeln!(f,
                 " at {}:{}:\n{}\n{: >indent$}",
                 self.row,
                 self.col - 1,
                 self.code.lines().nth(self.row - 1).unwrap(),
                 "^",
                 indent = self.col - 1
        )
    }
}

impl<'a, T> Pos<'a, T> {
    pub fn with<'b, U>(&'b self, inner: U) -> Pos<'a, U> {
        Pos {
            row: self.row,
            col: self.col,
            code: self.code,
            content: inner,
        }
    }

    pub fn extend<U>(mut self, other: &Pos<U>) -> Self {
        if other.row < self.row {
            self.row = other.row;
            self.col = other.col;
        } else if other.row == self.row && other.col < self.col {
            self.col = other.col;
        };

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
    fn join_with<'b, U>(&'b self, inner: U) -> Option<Pos<'a, U>>;
}

impl<'a, T> Join<'a> for Vec<Pos<'a, T>> {
    fn join_with<'b, U>(&'b self, inner: U) -> Option<Pos<'a, U>> {
        self
            .iter()
            .min_by(|p1, p2| if p1.row < p2.row {
                Ordering::Less
            } else if p1.row == p2.row {
                if p1.col < p2.col {
                    Ordering::Less
                } else if p1.col == p2.col {
                    Ordering::Equal
                } else {
                    Ordering::Greater
                }
            } else {
                Ordering::Greater
            })
            .map(|pos| pos.with(inner))
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
