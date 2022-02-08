use std::fmt::{Display, Formatter};

use crate::tokens::Token;

#[derive(Debug, Clone, PartialEq)]
pub enum Datum {
    Single(Token),
    List(Vec<Token>),
}

impl Display for Datum {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Datum::Single(t) => write!(f, "{}", t),
            Datum::List(t) => {
                write!(f, "(")?;
                for (i, t) in t.iter().enumerate() {
                    if i > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{}", t)?;
                }
                write!(f, ")")
            }
        }
    }
}
