use std::str::Chars;

use crate::position::Pos;

pub type CharIterator<'a> = Pos<'a, Chars<'a>>;

pub trait CharIterable<'a> {
    fn iter_char(self) -> CharIterator<'a>;
}

impl<'a> CharIterable<'a> for &'a str {
    fn iter_char(self) -> CharIterator<'a> {
        Pos::new(0, 0, self, self.chars())
    }
}

impl<'a> Iterator for CharIterator<'a> {
    type Item = Pos<'a, char>;

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.content.next()?;

        match next {
            '\n' => {
                self.row += 1;
                self.col = 0;
            }
            _ => self.col += 1
        }

        Some(Pos::new(self.row, self.col, self.code, next))
    }
}
