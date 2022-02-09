use crate::{datum::Datum, env::Env, builtins::{Value, Primitive, Procedure}, tokens::TokenKind};

pub fn eval(datum: &Datum, env: &mut Env) -> Value {
    match datum {
        Datum::Single(token) => {
            match &token.kind {
                TokenKind::Bool(b) => Value::Bool(*b),
                TokenKind::Number(n) => Value::Number(*n),
                TokenKind::Char(c) => Value::Char(*c),
                TokenKind::String(s) => Value::String(s.clone()),
                TokenKind::Ident(sym) => {
                    if let Some(value) = env.lookup(sym.clone()) {
                        value.clone()
                    } else {
                        panic!("Undefined symbol: {}", sym)
                    }
                },
                _ => unreachable!(), // If it reaches here, the parser is wrong.
            }
        }
        Datum::List(datum) => {
            if datum.is_empty() {
                panic!("Empty list")
            } else {
                let proc = eval(datum.first().unwrap(), env);
                match proc {
                    Value::Procedure(proc) => {
                        env.enter_frame();
                        let params = &datum[1..];
                        let args = &proc.params[..];

                        if params.len() != args.len() {
                            panic!("Wrong number of arguments")
                        }

                        for (param, arg) in params.iter().zip(args.iter()) {
                            let param = eval(param, env);
                            env.define(arg.clone(), param);
                        }

                        let ret = eval(&proc.body, env);
                        env.exit_frame();
                        ret
                    },
                    Value::BuiltinProcedure(proc) => {
                        let args = &datum[1..];
                        (proc.native)(args.iter().map(|arg| eval(arg, env)).collect())
                    },
                    Value::Primitive(prim) => {
                        match prim {
                            Primitive::Define => {
                                let symbol = datum[1].to_string();
                                let value = eval(&datum[2], env);
                                env.define(symbol, value);
                                Value::Void
                            },
                            Primitive::Set => {
                                let symbol = datum[1].to_string();
                                let value = eval(&datum[2], env);
                                if let Some(value_ref) = env.lookup(symbol.clone()) {
                                    *value_ref = value.clone();
                                } else {
                                    panic!("Undefined symbol: {}", symbol)
                                }
                                Value::Void
                            },
                            Primitive::If => {
                                let cond = eval(&datum[1], env);
                                if cond == Value::Bool(true) {
                                    eval(&datum[2], env)
                                } else {
                                    eval(&datum[3], env)
                                }
                            },
                            Primitive::Lambda => {
                                let params = match &datum[1] {
                                    Datum::List(params) => params.iter().map(|param| match param {
                                        Datum::Single(token) => {
                                            match token.kind.clone() {
                                                TokenKind::Ident(s) => s.clone(),
                                                _ => panic!("Invalid parameter name"),
                                            }
                                        },
                                        _ => panic!("Invalid parameter"),
                                    }).collect(),
                                    _ => panic!("Lambda expects a list of parameters"),
                                };
                                let body = &datum[2];
                                Value::Procedure(Procedure {
                                    params,
                                    body: body.clone(),
                                })
                            },
                        }
                    }
                    _ => panic!(),
                }
            }
        }
    }
}
