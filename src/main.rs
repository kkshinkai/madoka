mod source;
mod frontend;
mod diagnostic;
mod utils;

use std::{rc::Rc, cell::RefCell, io::{self, Write}};

use frontend::CompilationUnit;

use crate::{frontend::Lexer, source::BytePos, diagnostic::DiagnosticEngine};

fn main() {

    let mut unit = CompilationUnit::new();

    loop {
        print!("> ");
        io::stdout().flush().unwrap();

        let mut input = String::new();
        io::stdin()
            .read_line(&mut input)
            .expect("error: failed to readline");

        let file = unit.files.load_repl(input);

        unit.lex(file);
    }
}
