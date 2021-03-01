use std::iter::{Enumerate, FlatMap, Map, Repeat, Zip};
use std::str::Chars;

pub type CharIterator<'a> = FlatMap<Enumerate<TerminatedLines<'a>>, Map<Zip<Enumerate<Chars<'a>>, Repeat<usize>>, Reorder>, Position>;
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

impl<'a> CharIterable<'a> for &'a str {
    fn iter_char(&self) -> CharIterator<'a> {
        self.lines_terminated().enumerate().flat_map(position as Position)
    }
}

trait LineTerminatable<'a> {
    fn lines_terminated(self) -> TerminatedLines<'a>;
}

impl<'a> LineTerminatable<'a> for &'a str {
    fn lines_terminated(self) -> TerminatedLines<'a> {
        TerminatedLines { input: self }
    }
}

#[derive(Clone)]
pub struct TerminatedLines<'a> {
    input: &'a str,
}

impl<'a> Iterator for TerminatedLines<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        if self.input.is_empty() {
            None
        } else {
            let split = self.input.find('\n').map(|i| i + 1).unwrap_or(self.input.len());
            let (line, rest) = self.input.split_at(split);
            self.input = rest;
            Some(line)
        }
    }
}
