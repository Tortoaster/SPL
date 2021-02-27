use std::iter::{FlatMap, Enumerate, Map, Zip, Repeat};
use std::str::{Lines, Chars};

pub type CharIterator<'a> = FlatMap<Enumerate<Lines<'a>>, Map<Zip<Enumerate<Chars<'a>>, Repeat<usize>>, Reorder>, Position>;
type Position = fn((usize, &str)) -> Map<Zip<Enumerate<Chars>, Repeat<usize>>, Reorder>;
type Reorder = fn(((usize, char), usize)) -> ((usize, usize), char);

fn position((row, l): (usize, &str)) -> Map<Zip<Enumerate<Chars>, Repeat<usize>>, fn(((usize, char), usize)) -> ((usize, usize), char)> {
    l.chars().enumerate().zip(std::iter::repeat(row)).map(reorder)
}

fn reorder(((col, c), row): ((usize, char), usize)) -> ((usize, usize), char) {
    ((row, col), c)
}

pub trait CharIterable<'a> {
    fn iter_char(&self) -> CharIterator<'a>;
}

impl <'a> CharIterable<'a> for &'a str {
    fn iter_char(&self) -> CharIterator<'a> {
        self.lines().enumerate().flat_map(position as Position)
    }
}
