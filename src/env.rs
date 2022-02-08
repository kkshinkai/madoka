use std::collections::HashMap;

use crate::builtins::Value;

pub struct Env {
    frames: Vec<Frame>,
}

impl Env {
    pub fn new() -> Self {
        Env { frames: vec![] }
    }

    pub fn lookup(&mut self, symbol: String) -> Option<&mut Value> {
        for frame in self.frames.iter_mut().rev() {
            if let Some(value) = frame.lookup(symbol.as_str()) {
                return Some(value)
            }
        }
        None
    }

    pub fn enter_frame(&mut self) {
        self.frames.push(Frame::new());
    }

    pub fn exit_frame(&mut self) {
        self.frames.pop();
    }
}

pub struct Frame {
    bindings: HashMap<String, Value>,
}

impl Frame {
    pub fn new() -> Self {
        Frame { bindings: HashMap::new() }
    }

    pub fn define(&mut self, symbol: String, value: Value) {
        self.bindings.insert(symbol, value);
    }

    pub fn lookup(&mut self, symbol: &str) -> Option<&mut Value> {
        self.bindings.get_mut(symbol)
    }
}
