use std::str::Chars;

#[derive(Clone, Debug)]
pub struct CharIterator<'a> {
    chars: Chars<'a>,
    row: usize,
    col: usize
}

pub trait CharIterable<'a> {
    fn iter_char(&self) -> CharIterator<'a>;
}

impl<'a> CharIterable<'a> for &'a str {
    fn iter_char(&self) -> CharIterator<'a> {
        CharIterator {
            chars: self.chars(),
            row: 1,
            col: 1
        }
    }
}

impl<'a> Iterator for CharIterator<'a> {
    type Item = ((usize, usize), char);

    fn next(&mut self) -> Option<Self::Item> {
        let next = self.chars.next()?;

        match next {
            '\n' => {
                self.row += 1;
                self.col = 1;
            }
            _ => self.col += 1
        }

        Some(((self.row, self.col), next))
    }
}
