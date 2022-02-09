use std::fmt;

use crate::datum::Datum;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Bool(bool),
    Number(f64),
    Char(char),
    String(String),
    Procedure(Procedure),
    BuiltinProcedure(BuiltinProcedure),
    Primitive(Primitive),
    Void,
}

impl fmt::Display for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Bool(true) => write!(f, "#true"),
            Value::Bool(false) => write!(f, "#false"),
            Value::Number(n) => write!(f, "{}", n),
            Value::Char(c) => write!(f, "#\\{}", c),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::Procedure(_) => write!(f, "#<procedure>"),
            Value::BuiltinProcedure(_) => write!(f, "#<procedure>"),
            Value::Primitive(_) => write!(f, "#<primitive>"),
            Value::Void => write!(f, "#<void>"),
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Procedure {
    pub params: Vec<String>,
    pub body: Datum,
}


#[derive(Debug, Clone, PartialEq)]
pub struct BuiltinProcedure {
    pub native: fn(Vec<Value>) -> Value,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
    Define,
    Set,
    If,
    Lambda,
}
