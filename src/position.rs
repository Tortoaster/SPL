use std::cmp::Ordering;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

#[must_use]
#[derive(Clone, Eq, Debug)]
pub struct Pos<'a, T> {
    pub row: usize,
    pub col: usize,
    pub code: &'a str,
    pub inner: T,
}

impl<'a, T: PartialEq> PartialEq for Pos<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.inner == other.inner
    }
}

impl<'a, T: Hash> Hash for Pos<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.inner.hash(state)
    }
}

impl<'a, T> Pos<'a, T> {
    pub fn with<'b, U>(&'b self, inner: U) -> Pos<'a, U> {
        Pos {
            row: self.row,
            col: self.col,
            code: self.code,
            inner,
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
        (self.with(()), self.inner)
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
        &self.inner
    }
}

impl<'a, T> DerefMut for Pos<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}
