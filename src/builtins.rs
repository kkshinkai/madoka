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
}

#[derive(Debug, Clone, PartialEq)]
pub struct Procedure {
    params: Vec<String>,
    body: Vec<Datum>,
}


#[derive(Debug, Clone, PartialEq)]
pub struct BuiltinProcedure {
    native: fn(Vec<Value>) -> Value,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Primitive {
    Define,
    Set,
    If,
    Lambda,
}
