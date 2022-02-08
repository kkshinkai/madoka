use lexer::Lexer;

mod tokens;
mod lexer;

fn main() {
    let tokens = Lexer::new(r##""asdas" #\x #\alarm #true #f"##);
    tokens.for_each(|t| println!("{:?}", t));
}
