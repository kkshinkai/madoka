mod source;
mod frontend;
mod diagnostic;
mod utils;

use std::{rc::Rc, cell::RefCell};

use crate::{frontend::Lexer, source::BytePos, diagnostic::DiagnosticEngine};

fn main() {
    let src = r##"[\x123123123;]"##;

    let de = Rc::new(RefCell::new(DiagnosticEngine::new()));
    let _ = Lexer::new(src, BytePos::from_usize(0), de.clone())
        .collect::<Vec<_>>();
    de.borrow().emit();
}
