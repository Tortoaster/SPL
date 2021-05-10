use std::cmp::Ordering;
use std::fmt::Debug;
use std::hash::Hash;
use std::ops::{Deref, DerefMut};
use std::str::Chars;

#[must_use]
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct Pos<'a, T> {
    pub row: usize,
    pub col: usize,
    pub code: &'a str,
    pub inner: T,
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
    fn join_with<'b, U>(&'b self, inner: U) -> Pos<'a, U>;
}

impl<'a, T> Join<'a> for Vec<Pos<'a, T>> {
    fn join_with<'b, U>(&'b self, inner: U) -> Pos<'a, U> {
        let min = self
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
            .expect("cannot join positions of empty list");
        Pos {
            row: min.row,
            col: min.col,
            code: min.code,
            inner,
        }
    }
}

// impl<N> FromIterator<Positioned<N>> for Positioned<N> {
//     fn from_iter<T: IntoIterator<Item=Positioned<N>>>(iter: T) -> Self {
//         let min = iter
//             .into_iter()
//             .min_by(|p1, p2| if p1.row < p2.row {
//                 Ordering::Less
//             } else if p1.row == p2.row {
//                 if p1.col < p2.col {
//                     Ordering::Less
//                 } else if p1.col == p2.col {
//                     Ordering::Equal
//                 } else {
//                     Ordering::Greater
//                 }
//             } else {
//                 Ordering::Greater
//             })
//             .expect("cannot join positions of empty list");
//         Positioned {
//             row: min.row,
//             col: min.col,
//             code: min.code,
//             inner: iter
//                 .into_iter()
//                 .map(|pos| pos.inner)
//                 .collect(),
//         }
//     }
// }

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

pub type CharIterator<'a> = Pos<'a, Chars<'a>>;

pub trait CharIterable<'a> {
    fn iter_char(self) -> CharIterator<'a>;
}

impl<'a> CharIterable<'a> for &'a str {
    fn iter_char(self) -> CharIterator<'a> {
        Pos {
            row: 1,
            col: 1,
            code: self,
            inner: self.chars(),
        }
    }
}

impl<'a> Iterator for CharIterator<'a> {
    type Item = Pos<'a, char>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.inner.next()?;

        match next {
            '\n' => {
                self.row += 1;
                self.col = 1;
            }
            _ => self.col += 1
        }

        Some(Pos {
            row: self.row,
            col: self.col,
            code: self.code,
            inner: next,
        })
    }
}
