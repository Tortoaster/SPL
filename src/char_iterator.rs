use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::str::Chars;
use crate::parser::error::ParseError;
use crate::lexer::Token;

#[derive(Clone, Debug)]
pub struct Positioned<'a, K: Clone + Debug> {
    pub row: usize,
    pub col: usize,
    pub code: &'a str,
    pub inner: K,
}

impl<'a, K: Clone + Debug> Positioned<'a, K> {
    pub fn transform<N: Clone + Debug>(&self, inner: N) -> Positioned<'a, N> {
        Positioned {
            row: self.row,
            col: self.col,
            code: self.code,
            inner,
        }
    }
}

impl Positioned<'_, Token> {
    pub fn into_bad_token_err<S: AsRef<str>>(self, expected: S) -> ParseError {
        ParseError::BadToken {
            found: self.inner,
            row: self.row,
            col: self.col,
            code: self.code.to_owned(),
            expected: expected.as_ref().to_owned()
        }
    }
}

impl<'a, K: Clone + Debug> Deref for Positioned<'a, K> {
    type Target = K;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<'a, K: Clone + Debug> DerefMut for Positioned<'a, K> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

pub type CharIterator<'a> = Positioned<'a, Chars<'a>>;

pub trait CharIterable<'a> {
    fn iter_char(self) -> CharIterator<'a>;
}

impl<'a> CharIterable<'a> for &'a str {
    fn iter_char(self) -> CharIterator<'a> {
        Positioned {
            row: 1,
            col: 1,
            code: self,
            inner: self.chars(),
        }
    }
}

impl<'a> Iterator for CharIterator<'a> {
    type Item = Positioned<'a, char>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.inner.next()?;

        match next {
            '\n' => {
                self.row += 1;
                self.col = 1;
            }
            _ => self.col += 1
        }

        Some(Positioned {
            row: self.row,
            col: self.col,
            code: self.code,
            inner: next,
        })
    }
}
