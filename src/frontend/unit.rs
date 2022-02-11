use std::rc::Rc;

use crate::{source::{SourceMgr, SourceFile}, diagnostic::DiagnosticEngine};

#[derive(Debug, Clone, PartialEq)]
pub struct CompilationUnit {
    pub files: SourceMgr,
    pub diag: Rc<DiagnosticEngine>,
}

impl CompilationUnit {
    pub fn new() -> Self {
        CompilationUnit {
            files: SourceMgr::new(),
            diag: Rc::new(DiagnosticEngine::new()),
        }
    }

    fn lex(&mut self, file: Rc<SourceFile>) {
        let lexer = Lexer::new(file.src, file.start_pos, self.diag);
    }
}
