mod source;
mod frontend;
mod diagnostic;
mod utils;

use std::{rc::Rc, cell::RefCell};

use frontend::TokenOrTrivia;

use crate::{frontend::Lexer, source::BytePos, diagnostic::DiagnosticEngine};

fn main() {
    let src = r##"  "hello, world!\n"  "##;

    let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
    Lexer::new(src, BytePos::from_usize(0), de.clone()).for_each(|t| {
        println!("{:?} {}..{}", t.kind, t.span.start.to_usize(), t.span.end.to_usize());
    });

    de.borrow().emit();
}
