mod source;
mod frontend;
mod diagnostic;

// The following modules are used in the prototype and will be removed soon.
mod tokens;
mod lexer;
mod datum;
mod parser;
mod env;
mod builtins;
mod eval;

// use std::io::{self, Write};

// use builtins::{Value, Primitive, BuiltinProcedure};
// use parser::Parser;
// use eval::eval;

fn main() {

    // let mut env = env::Env::new();

    // env.enter_frame();
    // env.define("define".to_string(), Value::Primitive(Primitive::Define));
    // env.define("set!".to_string(), Value::Primitive(Primitive::Set));
    // env.define("if".to_string(), Value::Primitive(Primitive::If));
    // env.define("lambda".to_string(), Value::Primitive(Primitive::Lambda));
    // env.define("+".to_string(), Value::BuiltinProcedure(BuiltinProcedure {
    //     native : |x| {
    //         x.iter().fold(Value::Number(0.0), |acc, arg| {
    //             match (acc, arg) {
    //                 (Value::Number(a), Value::Number(b)) => Value::Number(a + b),
    //                 _ => panic!("+ expects numbers"),
    //             }
    //         })
    //     }
    // }));

    // env.define("display".to_string(), Value::BuiltinProcedure(BuiltinProcedure {
    //     native : |x| {
    //         if x.len() != 1 {
    //             panic!("display expects 1 argument")
    //         } else {
    //             println!("{}", x.first().unwrap());
    //             Value::Void
    //         }
    //     }
    // }));

    // let mut buffer = String::new();
    // let stdin = io::stdin();
    // let mut stdout = io::stdout();

    // loop {
    //     print!("> ");
    //     stdout.flush().expect("Failed to read line");
    //     stdin.read_line(&mut buffer).expect("Failed to read line");

    //     Parser::new(buffer.as_str())
    //         .parse()
    //         .iter()
    //         .for_each(|datum| println!("{}", eval(datum, &mut env)));

    //     buffer.clear();
    // }
}
