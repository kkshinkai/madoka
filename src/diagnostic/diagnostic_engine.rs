use crate::source::Span;

use super::diagnostic::{Diagnostic, Level};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DiagnosticEngine {
    pub diags: Vec<Diagnostic>,
}

impl DiagnosticEngine {
    pub fn new() -> Self {
        DiagnosticEngine {
            diags: Vec::new(),
        }
    }

    pub fn error(&mut self, span: Span, message: String) {
        self.diags.push(Diagnostic {
            level: Level::Error,
            message,
            span,
        });
    }

    pub fn warning(&mut self, span: Span, message: String) {
        self.diags.push(Diagnostic {
            level: Level::Warning,
            message,
            span,
        });
    }

    pub fn note(&mut self, span: Span, message: String) {
        self.diags.push(Diagnostic {
            level: Level::Note,
            message,
            span,
        });
    }
}

impl DiagnosticEngine {
    /// A temporary diagnostic printer.
    pub fn emit(&self) {
        for diag in &self.diags {
            let level = match diag.level {
                Level::Error => "error",
                Level::Warning => "warning",
                Level::Note => "note",
            };
            println!("{}: {}", level, diag.message);
        }
    }
}

