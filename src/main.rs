use lexer::Lexer;

mod tokens;
mod lexer;

fn main() {
    let tokens = Lexer::new(r##"(define x12 "asdas")"##);
    tokens.for_each(|t| println!("{:?}", t));
}
