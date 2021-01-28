use crate::lexer::Tokenize;

mod lexer;

fn main() {
    let code = "-327\t:   213  :   -324 :   []\n";

    for t in code.tokenize() {
        print!("{:?}", t)
    }
}
