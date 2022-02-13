use std::{rc::Rc, cell::RefCell};

use crate::{source::{SourceMgr, SourceFile}, diagnostic::DiagnosticEngine};

use super::{lexer::CharStream, Lexer};

#[derive(Debug, Clone, PartialEq)]
pub struct CompilationUnit {
    pub files: SourceMgr,
    pub diag: Rc<RefCell<DiagnosticEngine>>,
}

impl CompilationUnit {
    pub fn new() -> Self {
        CompilationUnit {
            files: SourceMgr::new(),
            diag: Rc::new(RefCell::new(DiagnosticEngine::new())),
        }
    }

    pub fn lex(&mut self, file: Rc<SourceFile>) {
        let lexer = Lexer::new(
            file.src.as_str(),
            file.start_pos,
            self.diag.clone()
        );

        let ts = lexer.collect::<Vec<_>>();

        if self.diag.borrow().has_error() {
            self.diag.borrow().emit();
        } else {
            ts.iter().for_each(|t| {
                println!("{:?} {}..{}", t.kind, t.span.start.to_usize(), t.span.end.to_usize());
            });
        }
    }
}
