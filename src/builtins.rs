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
