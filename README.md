# SPL Compiler

This is a work-in-progress compiler for the Simple Programming Language specification, written in Rust. Currently, it
features a simple lexer and parser. The operator precedence handling is done
using [Pratt parsing](https://en.wikipedia.org/wiki/Operator-precedence_parser).
See [this blog](https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html) for more details.
