use std::str::Chars;

use crate::position::Pos;

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
