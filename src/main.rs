mod tokens;
mod lexer;
mod datum;
mod parser;

use parser::Parser;

fn main() {
    let datums = Parser::new(r##"
    (define pi 3.14)
    (define (square x) (* x x))
    "##).parse();

    datums.iter().for_each(|datum|
        println!("{}", datum)
    );
}
