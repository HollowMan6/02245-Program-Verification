use miette::Result;
use std::collections::HashMap;
pub use syntax::{self, ast};

fn main() -> Result<()> {
    // Z3 usage example
    use z3::{ast::Int, SatResult};

    let cfg = z3::Config::new();
    let ctx = z3::Context::new(&cfg);

    // Parsing example
    for p in std::env::args().skip(1) {
        let doc_ast = syntax::parse_file(p)?;
        for item in doc_ast.items {
            match item {
                ast::DocumentItem::Method(method) => {
                    // Access fields of method
                    let ast::Method {
                        name: _,
                        inputs,
                        outputs,
                        specifications,
                        body,
                    } = method;

                    // Define variables hashmap and store it in context
                    let mut variables = HashMap::new();
                    parse_params(&ctx, &mut variables, inputs)?;
                    parse_params(&ctx, &mut variables, outputs)?;

                    match parse_specs(&ctx, &mut variables, specifications) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };

                    let b = match body {
                        Some(b) => b,
                        None => continue,
                    };
                    match parse_body(&ctx, &mut variables, b) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                }
                ast::DocumentItem::Function(function) => {
                    // Access fields of function
                    let ast::Function {
                        name: _,
                        inputs,
                        ret_ty: _,
                        specifications,
                        body,
                    } = function;

                    // Define variables hashmap and store it in context
                    let mut variables: HashMap<String, Variable> = HashMap::new();
                    parse_params(&ctx, &mut variables, inputs)?;

                    match parse_specs(&ctx, &mut variables, specifications) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                    match body {
                        Some(body) => {
                            parse_expr(&ctx, &mut variables, body);
                        }
                        None => continue,
                    }
                }
            }
        }
    }

    let solver = z3::Solver::new(&ctx);

    let x = Int::new_const(&ctx, "x");
    let zero = Int::from_i64(&ctx, 0);

    let assumptions = &[x.gt(&zero)];
    // Uncomment this for an unsatisfiable set of assumptions
    // let assumptions = &[x.gt(&zero), x.lt(&zero)];

    println!("Checking assumptions: {assumptions:?}");
    match solver.check_assumptions(assumptions) {
        SatResult::Unsat => {
            println!(" + The assertions were unsatisfiable!");
            for unsat in solver.get_unsat_core() {
                dbg!(unsat);
            }
        }
        SatResult::Unknown => {
            println!(" + Maybe the assertions were satisfiable?");
            if let Some(model) = solver.get_model() {
                dbg!(model);
            } else {
                println!("Oh no, couldn't extract a model!")
            }
        }
        SatResult::Sat => {
            println!(" + The assertions were satisfiable!");
            let model = solver
                .get_model()
                .expect("a model exists since we got 'Sat'");
            dbg!(model);
        }
    }

    Ok(())
}

#[derive(Clone)]
enum Variable<'a> {
    Bool(z3::ast::Bool<'a>),
    Int(z3::ast::Int<'a>),
}

#[derive(Clone)]
enum Value<'a> {
    Bool(bool),
    Int(i64),
    Var(Variable<'a>),
}

fn parse_type<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    name: String,
    ty: ast::Type,
) {
    let variable = match ty {
        ast::Type::Bool => Variable::Bool(z3::ast::Bool::new_const(&ctx, name.clone())),
        ast::Type::Int => Variable::Int(z3::ast::Int::new_const(&ctx, name.clone())),
    };
    variables.insert(name, variable);
}

fn parse_params<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    params: Vec<ast::Var>,
) -> Result<()> {
    for param in params {
        let ast::Var { name, ty } = param;
        parse_type(&ctx, variables, name.text, ty);
    }
    Ok(())
}

// Parse specifications
fn parse_specs<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    specs: Vec<ast::Specification>,
) -> Result<()> {
    for spec in specs {
        let value = match spec {
            ast::Specification::Ensures(ensures) => match parse_expr(&ctx, variables, ensures) {
                Ok(value) => value,
                Err(_) => continue,
            },
            ast::Specification::Requires(requires) => match parse_expr(&ctx, variables, requires) {
                Ok(value) => value,
                Err(_) => continue,
            },
        };
    }
    Ok(())
}

fn parse_expr<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    expr: ast::Expr,
) -> Result<Value<'a>, String> {
    let kind = expr.kind;
    let ty = expr.ty;
    // match ty {
    //     ast::Type::Bool => Ok(Value::Bool(true)),
    //     ast::Type::Int => Ok(Value::Int(0)),
    // };
    match parse_expr_kind(&ctx, variables, kind) {
        Ok(value) => Ok(value),
        Err(_) => Err("Unexpected expression type".to_string()),
    }
}

fn parse_expr_kind<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    expr_kind: Box<ast::ExprKind>,
) -> Result<Value<'a>, String> {
    match *expr_kind {
        ast::ExprKind::Boolean(b) => Ok(Value::Bool(b)),
        ast::ExprKind::Integer(i) => Ok(Value::Int(i.parse().unwrap())),
        ast::ExprKind::Result => Ok(Value::Bool(true)),
        ast::ExprKind::Var(ident) => Ok(Value::Var(variables.get(&ident.text).unwrap().clone())),
        ast::ExprKind::Call(ident, exprs) => {
            println!("Call: {}", ident.text);
            for expr in exprs {
                // TODO: handle multiple exprs
                parse_expr(&ctx, variables, expr);
            }
            Ok(Value::Var(variables.get(&ident.text).unwrap().clone()))
        }
        ast::ExprKind::Unary(uop, expr) => match parse_expr(&ctx, variables, expr) {
            Ok(value) => match uop {
                ast::UOp::Minus => match value {
                    Value::Int(i) => Ok(Value::Int(-i)),
                    Value::Var(var) => match var {
                        Variable::Int(i) => Ok(Value::Var(Variable::Int(i.unary_minus()))),
                        _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                    },
                    _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                },
                ast::UOp::Not => match value {
                    Value::Bool(i) => Ok(Value::Bool(!i)),
                    Value::Var(var) => match var {
                        Variable::Bool(i) => Ok(Value::Var(Variable::Bool(i.not()))),
                        _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                    },
                    _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                },
            },
            Err(e) => Err(e),
        },
        ast::ExprKind::Binary(expr1, op, expr2) => {
            // Give some example for this you have in mind?
            match parse_expr(&ctx, variables, expr1) {
                Ok(value1) => match parse_expr(&ctx, variables, expr2) {
                    Ok(value2) => match op {
                        ast::Op::And => match value1 {
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 && var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => {
                                        Ok(Value::Var(Variable::Bool(z3::ast::Bool::and(
                                            ctx,
                                            &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                        ))))
                                    }
                                    _ => Err("&& with a value that has wrong type".to_string()),
                                },
                                _ => Err("&& with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok(Value::Var(Variable::Bool(z3::ast::Bool::and(
                                            ctx,
                                            &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                        ))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => Ok(Value::Var(Variable::Bool(
                                            z3::ast::Bool::and(ctx, &[&i, &i2]),
                                        ))),
                                        _ => Err("&& with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("&& with a value that has wrong type".to_string()),
                                },
                                _ => Err("&& with a value that has wrong type".to_string()),
                            },
                            _ => Err("&& with a value that has wrong type".to_string()),
                        },
                        ast::Op::Divide => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Int(var1 / var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => Ok(Value::Var(Variable::Int(
                                        z3::ast::Int::from_i64(ctx, var1).div(&i),
                                    ))),
                                    _ => Err("/ with a value that has wrong type".to_string()),
                                },
                                _ => Err("/ with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Int(
                                        i.div(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Int(i.div(&i2))))
                                        }
                                        _ => Err("/ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("/ with a value that has wrong type".to_string()),
                                },
                                _ => Err("/ with a value that has wrong type".to_string()),
                            },
                            _ => Err("/ with a value that has wrong type".to_string()),
                        },
                        ast::Op::Eq => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 == var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => {
                                        Ok(Value::Bool(z3::ast::Int::from_i64(ctx, var1).eq(&i)))
                                    }
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                _ => Err("== with a value that has wrong type".to_string()),
                            },
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 == var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => {
                                        Ok(Value::Bool(z3::ast::Bool::from_bool(ctx, var1).eq(&i)))
                                    }
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                _ => Err("== with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => {
                                        Ok(Value::Bool(i.eq(&z3::ast::Int::from_i64(ctx, var2))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => Ok(Value::Bool(i.eq(&i2))),
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok(Value::Bool(i.eq(&z3::ast::Bool::from_bool(ctx, var2))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => Ok(Value::Bool(i.eq(&i2))),
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                _ => Err("== with a value that has wrong type".to_string()),
                            },
                            _ => Err("== with a value that has wrong type".to_string()),
                        },
                        ast::Op::Geq => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 >= var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1).ge(&i),
                                    ))),
                                    _ => Err(">= with a value that has wrong type".to_string()),
                                },
                                _ => Err(">= with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i.ge(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i.ge(&i2))))
                                        }
                                        _ => Err(">= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err(">= with a value that has wrong type".to_string()),
                                },
                                _ => Err(">= with a value that has wrong type".to_string()),
                            },
                            _ => Err(">= with a value that has wrong type".to_string()),
                        },
                        ast::Op::Gt => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 > var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1).gt(&i),
                                    ))),
                                    _ => Err("> with a value that has wrong type".to_string()),
                                },
                                _ => Err("> with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i.gt(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i.gt(&i2))))
                                        }
                                        _ => Err("> with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("> with a value that has wrong type".to_string()),
                                },
                                _ => Err("> with a value that has wrong type".to_string()),
                            },
                            _ => Err("> with a value that has wrong type".to_string()),
                        },
                        ast::Op::Implies => match value1 {
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Var(Variable::Bool(
                                    z3::ast::Bool::from_bool(ctx, var1)
                                        .implies(&z3::ast::Bool::from_bool(ctx, var2)),
                                ))),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Bool::from_bool(ctx, var1).implies(&i),
                                    ))),
                                    _ => Err("==> with a value that has wrong type".to_string()),
                                },
                                _ => Err("==> with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => Ok(Value::Var(Variable::Bool(
                                        i.implies(&z3::ast::Bool::from_bool(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => {
                                            Ok(Value::Var(Variable::Bool(i.implies(&i2))))
                                        }
                                        _ => {
                                            Err("==> with a value that has wrong type".to_string())
                                        }
                                    },
                                    _ => Err("==> with a value that has wrong type".to_string()),
                                },
                                _ => Err("==> with a value that has wrong type".to_string()),
                            },
                            _ => Err("==> with a value that has wrong type".to_string()),
                        },
                        ast::Op::Leq => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 <= var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1).le(&i),
                                    ))),
                                    _ => Err("<= with a value that has wrong type".to_string()),
                                },
                                _ => Err("<= with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i.le(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i.le(&i2))))
                                        }
                                        _ => Err("<= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("<= with a value that has wrong type".to_string()),
                                },
                                _ => Err("<= with a value that has wrong type".to_string()),
                            },
                            _ => Err("<= with a value that has wrong type".to_string()),
                        },
                        ast::Op::Lt => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 < var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1).lt(&i),
                                    ))),
                                    _ => Err("< with a value that has wrong type".to_string()),
                                },
                                _ => Err("< with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i.lt(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i.lt(&i2))))
                                        }
                                        _ => Err("< with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("< with a value that has wrong type".to_string()),
                                },
                                _ => Err("< with a value that has wrong type".to_string()),
                            },
                            _ => Err("< with a value that has wrong type".to_string()),
                        },
                        ast::Op::Minus => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Int(var1 - var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::sub(
                                            ctx,
                                            &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                        ))))
                                    }
                                    _ => Err("- with a value that has wrong type".to_string()),
                                },
                                _ => Err("- with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::sub(
                                            ctx,
                                            &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                        ))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => Ok(Value::Var(Variable::Int(
                                            z3::ast::Int::sub(ctx, &[&i, &i2]),
                                        ))),
                                        _ => Err("- with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("- with a value that has wrong type".to_string()),
                                },
                                _ => Err("- with a value that has wrong type".to_string()),
                            },
                            _ => Err("- with a value that has wrong type".to_string()),
                        },
                        ast::Op::Neq => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Bool(var1 != var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => {
                                        Ok(Value::Bool(z3::ast::Int::from_i64(ctx, var1).ne(&i)))
                                    }
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 != var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => {
                                        Ok(Value::Bool(z3::ast::Bool::from_bool(ctx, var1).ne(&i)))
                                    }
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => {
                                        Ok(Value::Bool(i.ne(&z3::ast::Int::from_i64(ctx, var2))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => Ok(Value::Bool(i.ne(&i2))),
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok(Value::Bool(i.ne(&z3::ast::Bool::from_bool(ctx, var2))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => Ok(Value::Bool(i.ne(&i2))),
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            _ => Err("!= with a value that has wrong type".to_string()),
                        },
                        ast::Op::Or => match value1 {
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 || var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => {
                                        Ok(Value::Var(Variable::Bool(z3::ast::Bool::or(
                                            ctx,
                                            &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                        ))))
                                    }
                                    _ => Err("|| with a value that has wrong type".to_string()),
                                },
                                _ => Err("|| with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok(Value::Var(Variable::Bool(z3::ast::Bool::or(
                                            ctx,
                                            &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                        ))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => Ok(Value::Var(Variable::Bool(
                                            z3::ast::Bool::or(ctx, &[&i, &i2]),
                                        ))),
                                        _ => Err("|| with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("|| with a value that has wrong type".to_string()),
                                },
                                _ => Err("|| with a value that has wrong type".to_string()),
                            },
                            _ => Err("|| with a value that has wrong type".to_string()),
                        },
                        ast::Op::Plus => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Int(var1 + var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::add(
                                            ctx,
                                            &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                        ))))
                                    }
                                    _ => Err("+ with a value that has wrong type".to_string()),
                                },
                                _ => Err("+ with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::add(
                                            ctx,
                                            &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                        ))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => Ok(Value::Var(Variable::Int(
                                            z3::ast::Int::add(ctx, &[&i, &i2]),
                                        ))),
                                        _ => Err("+ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("+ with a value that has wrong type".to_string()),
                                },
                                _ => Err("+ with a value that has wrong type".to_string()),
                            },
                            _ => Err("+ with a value that has wrong type".to_string()),
                        },
                        ast::Op::Times => match value1 {
                            Value::Int(var1) => match value2 {
                                Value::Int(var2) => Ok(Value::Int(var1 * var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Int(i) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::mul(
                                            ctx,
                                            &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                        ))))
                                    }
                                    _ => Err("* with a value that has wrong type".to_string()),
                                },
                                _ => Err("* with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => {
                                        Ok(Value::Var(Variable::Int(z3::ast::Int::mul(
                                            ctx,
                                            &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                        ))))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => Ok(Value::Var(Variable::Int(
                                            z3::ast::Int::mul(ctx, &[&i, &i2]),
                                        ))),
                                        _ => Err("* with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("* with a value that has wrong type".to_string()),
                                },
                                _ => Err("* with a value that has wrong type".to_string()),
                            },
                            _ => Err("* with a value that has wrong type".to_string()),
                        },
                    },
                    Err(e) => Err(e),
                },
                Err(e) => Err(e),
            }
        }
        ast::ExprKind::Quantification(quantifier, var, expr) => {
            match quantifier {
                ast::Quantifier::Forall => {
                    println!("Quantifier: Forall");
                }
                ast::Quantifier::Exists => {
                    println!("Quantifier: Exists");
                }
            }
            let ast::Var { name, ty } = var;
            println!("Var: {}", name.text);
            parse_type(&ctx, variables, name.text, ty);
            match parse_expr(&ctx, variables, expr) {
                Ok(value) => Ok(value),
                Err(e) => Err(e),
            }
        }
    }
}

// Parse body
fn parse_body<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    body: ast::Body,
) -> Result<()> {
    for stmt in body.statements {
        match stmt {
            ast::Statement::Var(var, expr) => {
                let ast::Var { name, ty } = var;
                println!("Var: {}", name.text);
                parse_type(&ctx, variables, name.text, ty);
                match expr {
                    Some(expr) => {
                        match parse_expr(&ctx, variables, expr) {
                            Ok(_value) => {}
                            Err(_) => continue,
                        };
                    }
                    None => continue,
                }
            }
            ast::Statement::Assert(expr) => {
                match parse_expr(&ctx, variables, expr) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::Assume(expr) => {
                match parse_expr(&ctx, variables, expr) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::Assignment(ident, expr) => {
                println!("Assignment: {}", ident.text);
                match parse_expr(&ctx, variables, expr) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::MethodAssignment(idents, ident, exprs) => {
                println!("MethodAssignment: {}", ident.text);
                for ident in idents {
                    println!("Var: {}", ident.text);
                }
                for expr in exprs {
                    match parse_expr(&ctx, variables, expr) {
                        Ok(_value) => {}
                        Err(_) => continue,
                    };
                }
            }
            ast::Statement::If(expr, body, body_opt) => {
                match parse_expr(&ctx, variables, expr) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
                match parse_body(&ctx, variables, body) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
                match body_opt {
                    Some(body) => {
                        match parse_body(&ctx, variables, body) {
                            Ok(()) => {}
                            Err(_) => continue,
                        };
                    }
                    None => continue,
                }
            }
            ast::Statement::While {
                condition,
                invariants,
                body,
            } => {
                match parse_expr(&ctx, variables, condition) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
                for invariant in invariants {
                    match parse_expr(&ctx, variables, invariant) {
                        Ok(_value) => {}
                        Err(_) => continue,
                    };
                }
                match parse_body(&ctx, variables, body) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
        }
    }
    Ok(())
}
