use std::{rc::Rc, cell::RefCell};

use crate::{source::{SourceMgr, SourceFile}, diagnostic::DiagnosticEngine};

use super::lexer::CharStream;

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
}
