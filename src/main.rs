mod tokens;
mod lexer;
mod datum;
mod parser;
mod env;
mod builtins;
mod eval;

use builtins::{Value, Primitive, BuiltinProcedure};
use parser::Parser;
use eval::eval;

fn main() {
    let mut env = env::Env::new();

    env.enter_frame();
    env.define("define".to_string(), Value::Primitive(Primitive::Define));
    env.define("set".to_string(), Value::Primitive(Primitive::Set));
    env.define("if".to_string(), Value::Primitive(Primitive::If));
    env.define("lambda".to_string(), Value::Primitive(Primitive::Lambda));
    env.define("+".to_string(), Value::BuiltinProcedure(BuiltinProcedure {
        native : |x| {
            x.iter().fold(Value::Number(0.0), |acc, arg| {
                match (acc, arg) {
                    (Value::Number(a), Value::Number(b)) => Value::Number(a + b),
                    _ => panic!("+ expects numbers"),
                }
            })
        }
    }));

    env.define("display".to_string(), Value::BuiltinProcedure(BuiltinProcedure {
        native : |x| {
            if x.len() != 1 {
                panic!("display expects 1 argument")
            } else {
                println!("{}", match x.first().unwrap() {
                    Value::String(s) => s.clone(),
                    Value::Bool(true) => "#true".to_string(),
                    Value::Bool(false) => "#false".to_string(),
                    Value::Number(n) => n.to_string(),
                    Value::Char(c) => c.to_string(),
                    Value::BuiltinProcedure(_) | Value::Procedure(_) =>
                        "#<procedure>".to_string(),
                    Value::Void => "#<void>".to_string(),
                    Value::Primitive(_) => panic!("display expects a value"),
                });
                Value::Void
            }
        }
    }));


    Parser::new(r##"
    (define inc (lambda (x) (+ x 1)))

    (display (inc (inc 42)))
    "##).parse().iter().for_each(|datum| {
        eval(datum, &mut env);
    });
}
