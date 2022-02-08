use lexer::Lexer;

mod tokens;
mod lexer;

fn main() {
    let mut tokens = Lexer::new("( \"asdas\"");
    println!("{:?}", tokens.next());
    tokens.for_each(|t| println!("{:?}", t));
}
