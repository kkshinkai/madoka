use lexer::Lexer;

mod tokens;
mod lexer;

fn main() {
    let tokens = Lexer::new(r##"(define pi 3.14)"##);
    tokens.for_each(|t| println!("{:?}", t));
}
