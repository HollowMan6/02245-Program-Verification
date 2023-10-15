use miette::Result;
use std::collections::HashMap;
pub use syntax::ast;
use z3::ast::Ast;

fn main() -> Result<()> {
    // Parsing
    for p in std::env::args().skip(1) {
        let doc_ast = syntax::parse_file(p.clone())?;
        for item in doc_ast.items {
            let cfg = z3::Config::new();
            let ctx = z3::Context::new(&cfg);
            let solver = z3::Solver::new(&ctx);
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
                    parse_params(&ctx, &mut variables, inputs);
                    parse_params(&ctx, &mut variables, outputs);

                    match parse_specs(&ctx, &mut variables, specifications) {
                        Ok((require, ensure)) => {
                            let mut assumptions: Vec<z3::ast::Bool> = vec![require];
                            match body {
                                Some(b) => {
                                    match parse_body(
                                        &ctx,
                                        &mut variables,
                                        &solver,
                                        assumptions.clone(),
                                        b,
                                    ) {
                                        Ok(a) => {
                                            assumptions = a;
                                            println!("The body of file {p} parsed successfully");
                                        }
                                        Err(e) => {
                                            println!("{e}")
                                        }
                                    };
                                }
                                None => {}
                            }
                            solver.assert(&ensure);
                            match add_assumption(&ctx, &solver, assumptions, Value::None) {
                                Ok(_) => {}
                                Err(e) => println!("{e}"),
                            }
                        }
                        Err(e) => {
                            println!("{e}")
                        }
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
                    parse_params(&ctx, &mut variables, inputs);

                    match parse_specs(&ctx, &mut variables, specifications) {
                        Ok((require, ensure)) => {
                            let mut assumptions: Vec<z3::ast::Bool> = vec![require];
                            match body {
                                Some(body) => {
                                    // TODO: Add support for functions calling check
                                    match match parse_expr(&ctx, &mut variables, body) {
                                        Ok(value) => add_assumption(
                                            &ctx,
                                            &solver,
                                            assumptions.clone(),
                                            value,
                                        ),
                                        Err(e) => Err(e),
                                    } {
                                        Ok(a) => {
                                            assumptions = a;
                                            println!(
                                                "The function of file {p} parsed successfully"
                                            );
                                        }
                                        Err(e) => {
                                            println!("{e}")
                                        }
                                    };
                                }
                                None => {}
                            }
                            solver.assert(&ensure);
                            match add_assumption(&ctx, &solver, assumptions, Value::None) {
                                Ok(_) => {}
                                Err(e) => println!("{e}"),
                            }
                        }
                        Err(e) => {
                            println!("{e}")
                        }
                    };
                }
            }
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
    None,
}

fn assume<'a>(
    solver: &z3::Solver<'a>,
    assumptions: &[z3::ast::Bool],
) -> Result<z3::Model<'a>, String> {
    dbg!(assumptions);
    match solver.check_assumptions(assumptions) {
        z3::SatResult::Unsat => {
            for unsat in solver.get_unsat_core() {
                dbg!(unsat);
            }
            Err(" + The assertions were unsatisfiable!".to_string())
        }
        z3::SatResult::Unknown => {
            if let Some(model) = solver.get_model() {
                return Ok(model);
            }
            Err(" + The assertions may be satisfiable but couldn't extract a model".to_string())
        }
        z3::SatResult::Sat => {
            println!(" + The assertions were satisfiable!");
            let model = solver
                .get_model()
                .expect("a model exists since we got 'Sat'");
            Ok(model)
        }
    }
}

fn add_assumption<'a>(
    ctx: &'a z3::Context,
    solver: &z3::Solver,
    assumptions: Vec<z3::ast::Bool<'a>>,
    assumption: Value<'a>,
) -> Result<Vec<z3::ast::Bool<'a>>, String> {
    let mut new_assumptions = Vec::new();
    let actual_assumption = match assumption {
        Value::Bool(b) => Some(z3::ast::Bool::from_bool(ctx, b)),
        Value::Var(var) => match var {
            Variable::Bool(b) => Some(b),
            _ => return Err("assumption with a value that is not boolean".to_string()),
        },
        Value::None => None,
        _ => return Err("assumption with a value that is not boolean".to_string()),
    };
    match actual_assumption {
        Some(a) => {
            for ass in assumptions {
                new_assumptions.push(ass.implies(&a))
            }
        }
        None => new_assumptions = assumptions,
    }
    match assume(solver, &new_assumptions) {
        Ok(model) => {
            dbg!(model);
            Ok(new_assumptions)
        }
        Err(e) => Err(e),
    }
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
) {
    for param in params {
        let ast::Var { name, ty } = param;
        parse_type(&ctx, variables, name.text, ty);
    }
}

// Parse specifications
fn parse_specs<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    specs: Vec<ast::Specification>,
) -> Result<(z3::ast::Bool<'a>, z3::ast::Bool<'a>), String> {
    let mut requires = Vec::new();
    let mut ensures = Vec::new();
    for spec in specs {
        match spec {
            ast::Specification::Ensures(e) => match parse_expr(&ctx, variables, e) {
                Ok(value) => match value {
                    Value::Bool(b) => ensures.push(z3::ast::Bool::from_bool(ctx, b)),
                    Value::Var(var) => match var {
                        Variable::Bool(b) => ensures.push(b),
                        _ => return Err("Ensures with a value that has wrong type".to_string()),
                    },
                    _ => return Err("Ensures with a value that has wrong type".to_string()),
                },
                Err(e) => return Err(e),
            },
            ast::Specification::Requires(r) => match parse_expr(&ctx, variables, r) {
                Ok(value) => match value {
                    Value::Bool(b) => requires.push(z3::ast::Bool::from_bool(ctx, b)),
                    Value::Var(var) => match var {
                        Variable::Bool(b) => requires.push(b),
                        _ => return Err("Requires with a value that has wrong type".to_string()),
                    },
                    _ => return Err("Requires with a value that has wrong type".to_string()),
                },
                Err(e) => return Err(e),
            },
        };
    }
    let mut require = match requires.pop() {
        Some(r) => r,
        None => z3::ast::Bool::from_bool(ctx, true),
    };
    while requires.len() > 0 {
        require = match requires.pop() {
            Some(r) => z3::ast::Bool::and(ctx, &[&require, &r]),
            None => require,
        };
    }
    let mut ensure = match ensures.pop() {
        Some(r) => r,
        None => z3::ast::Bool::from_bool(ctx, true),
    };
    while ensures.len() > 0 {
        ensure = match ensures.pop() {
            Some(r) => z3::ast::Bool::and(ctx, &[&ensure, &r]),
            None => ensure,
        };
    }

    Ok((require, ensure))
}

fn parse_expr<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    expr: ast::Expr,
) -> Result<Value<'a>, String> {
    let kind = expr.kind;
    // let ty = expr.ty;
    // match ty {
    //     ast::Type::Bool => Ok(Value::Bool(true)),
    //     ast::Type::Int => Ok(Value::Int(0)),
    // };
    match parse_expr_kind(&ctx, variables, kind) {
        Ok(value) => Ok(value),
        Err(e) => Err(e),
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
        // TODO: handle result, var and call
        ast::ExprKind::Result => Ok(Value::Bool(true)),
        ast::ExprKind::Var(ident) => Ok(Value::Var(variables.get(&ident.text).unwrap().clone())),
        ast::ExprKind::Call(ident, exprs) => {
            println!("Call: {}", ident.text);
            for expr in exprs {
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
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1)._eq(&i),
                                    ))),
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                _ => Err("== with a value that has wrong type".to_string()),
                            },
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 == var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Bool::from_bool(ctx, var1)._eq(&i),
                                    ))),
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                _ => Err("== with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i._eq(&z3::ast::Int::from_i64(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i._eq(&i2))))
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => Ok(Value::Var(Variable::Bool(
                                        i._eq(&z3::ast::Bool::from_bool(ctx, var2)),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => {
                                            Ok(Value::Var(Variable::Bool(i._eq(&i2))))
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                // _ => Err("== with a value that has wrong type".to_string()),
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
                                    Variable::Int(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Int::from_i64(ctx, var1)._eq(&i).not(),
                                    ))),
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            Value::Bool(var1) => match value2 {
                                Value::Bool(var2) => Ok(Value::Bool(var1 != var2)),
                                Value::Var(var2) => match var2 {
                                    Variable::Bool(i) => Ok(Value::Var(Variable::Bool(
                                        z3::ast::Bool::from_bool(ctx, var1)._eq(&i).not(),
                                    ))),
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            Value::Var(var) => match var {
                                Variable::Int(i) => match value2 {
                                    Value::Int(var2) => Ok(Value::Var(Variable::Bool(
                                        i._eq(&z3::ast::Int::from_i64(ctx, var2)).not(),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i2) => {
                                            Ok(Value::Var(Variable::Bool(i._eq(&i2).not())))
                                        }
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                Variable::Bool(i) => match value2 {
                                    Value::Bool(var2) => Ok(Value::Var(Variable::Bool(
                                        i._eq(&z3::ast::Bool::from_bool(ctx, var2)).not(),
                                    ))),
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i2) => {
                                            Ok(Value::Var(Variable::Bool(i._eq(&i2).not())))
                                        }
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                // _ => Err("!= with a value that has wrong type".to_string()),
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
            let ast::Var { name, ty } = var;
            println!("Var: {}", name.text);
            parse_type(&ctx, variables, name.text.clone(), ty);
            match parse_expr(&ctx, variables, expr) {
                Ok(value) => {
                    let body = match value {
                        Value::Bool(b) => z3::ast::Bool::from_bool(ctx, b),
                        Value::Var(var) => match var {
                            Variable::Bool(b) => b,
                            _ => {
                                return Err(
                                    "Quantification with a value that has wrong type".to_string()
                                )
                            }
                        },
                        _ => {
                            return Err(
                                "Quantification with a value that has wrong type".to_string()
                            )
                        }
                    };
                    match quantifier {
                        ast::Quantifier::Forall => {
                            match variables.get(&name.text).unwrap().clone() {
                                Variable::Bool(bound) => Ok(Value::Var(Variable::Bool(
                                    z3::ast::forall_const(ctx, &[&bound], &[], &body),
                                ))),
                                Variable::Int(bound) => Ok(Value::Var(Variable::Bool(
                                    z3::ast::forall_const(ctx, &[&bound], &[], &body),
                                ))),
                            }
                        }
                        ast::Quantifier::Exists => {
                            match variables.get(&name.text).unwrap().clone() {
                                Variable::Bool(bound) => Ok(Value::Var(Variable::Bool(
                                    z3::ast::exists_const(ctx, &[&bound], &[], &body),
                                ))),
                                Variable::Int(bound) => Ok(Value::Var(Variable::Bool(
                                    z3::ast::exists_const(ctx, &[&bound], &[], &body),
                                ))),
                            }
                        }
                    }
                }
                Err(e) => Err(e),
            }
        }
    }
}

// Parse body
fn parse_body<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    solver: &z3::Solver,
    assumptions: Vec<z3::ast::Bool<'a>>,
    body: ast::Body,
) -> Result<Vec<z3::ast::Bool<'a>>, String> {
    let mut assumptions = assumptions;
    for stmt in body.statements {
        assumptions = match match stmt {
            ast::Statement::Var(var, expr) => {
                let ast::Var { name, ty } = var;
                parse_type(&ctx, variables, name.text.clone(), ty);
                match expr {
                    Some(expr) => parse_assignment(ctx, variables, solver, assumptions, name, expr),
                    None => Ok(assumptions),
                }
            }
            ast::Statement::Assert(expr) => match parse_expr(&ctx, variables, expr) {
                Ok(value) => match value {
                    Value::Bool(b) => {
                        solver.assert(&z3::ast::Bool::from_bool(ctx, b));
                        add_assumption(ctx, solver, assumptions, Value::None)
                    }
                    Value::Var(var) => match var {
                        Variable::Bool(b) => {
                            solver.assert(&b);
                            add_assumption(ctx, solver, assumptions, Value::None)
                        }
                        _ => return Err("Assert with a value that has wrong type".to_string()),
                    },
                    _ => return Err("Assert with a value that has wrong type".to_string()),
                },
                Err(e) => return Err(e),
            },
            ast::Statement::Assume(expr) => match parse_expr(&ctx, variables, expr) {
                Ok(value) => match value.clone() {
                    Value::Bool(b) => add_assumption(
                        ctx,
                        solver,
                        assumptions.clone(),
                        Value::Var(Variable::Bool(z3::ast::Bool::from_bool(ctx, b))),
                    ),
                    Value::Var(var) => match var {
                        Variable::Bool(_) => {
                            add_assumption(ctx, solver, assumptions.clone(), value)
                        }
                        _ => return Err("Assume with a value that has wrong type".to_string()),
                    },
                    _ => return Err("Assume with a value that has wrong type".to_string()),
                },
                Err(e) => return Err(e),
            },
            ast::Statement::Assignment(ident, expr) => {
                parse_assignment(ctx, variables, solver, assumptions, ident, expr)
            }
            ast::Statement::MethodAssignment(idents, ident, exprs) => {
                // TODO: Support method assignment
                println!("MethodAssignment: {}", ident.text);
                for ident in idents {
                    println!("Var: {}", ident.text);
                }
                for expr in exprs {
                    match parse_expr(&ctx, variables, expr) {
                        Ok(value) => {}
                        Err(e) => return Err(e),
                    };
                }
                Ok(assumptions)
            }
            ast::Statement::If(expr, body, body_opt) => match parse_expr(&ctx, variables, expr) {
                Ok(value) => {
                    let assumptions_if =
                        match add_assumption(ctx, solver, assumptions.clone(), value.clone()) {
                            Ok(if_ass) => match parse_body(&ctx, variables, solver, if_ass, body) {
                                Ok(a) => a,
                                Err(e) => return Err(e),
                            },
                            Err(e) => return Err(e),
                        };
                    match body_opt {
                        Some(body) => {
                            match match value {
                                Value::Bool(b) => Ok(Value::Bool(!b)),
                                Value::Var(var) => match var {
                                    Variable::Bool(b) => Ok(Value::Var(Variable::Bool(b.not()))),
                                    _ => {
                                        Err("if condition with a value that has wrong type"
                                            .to_string())
                                    }
                                },
                                _ => {
                                    Err("if condition with a value that has wrong type".to_string())
                                }
                            } {
                                Ok(else_ass) => {
                                    match add_assumption(ctx, solver, assumptions, else_ass) {
                                        Ok(else_assumptions) => match parse_body(
                                            &ctx,
                                            variables,
                                            solver,
                                            else_assumptions,
                                            body,
                                        ) {
                                            Ok(final_ass) => {
                                                Ok(vec![assumptions_if.clone(), final_ass].concat())
                                            }
                                            Err(e) => Err(e),
                                        },
                                        Err(e) => Err(e),
                                    }
                                }
                                Err(e) => Err(e),
                            }
                        }
                        None => Ok(assumptions_if),
                    }
                }
                Err(e) => return Err(e),
            },
            ast::Statement::While {
                condition,
                invariants,
                body,
            } => {
                // TODO: Support while
                match parse_expr(&ctx, variables, condition) {
                    Ok(value) => {}
                    Err(e) => return Err(e),
                };
                for invariant in invariants {
                    match parse_expr(&ctx, variables, invariant) {
                        Ok(value) => {}
                        Err(e) => return Err(e),
                    };
                }
                parse_body(&ctx, variables, solver, assumptions.clone(), body)
            }
        } {
            Ok(a) => a,
            Err(e) => return Err(e),
        }
    }
    Ok(assumptions)
}

fn parse_assignment<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    solver: &z3::Solver,
    assumptions: Vec<z3::ast::Bool<'a>>,
    ident: ast::Ident,
    expr: ast::Expr,
) -> Result<Vec<z3::ast::Bool<'a>>, String> {
    match variables.clone().get(&ident.text).unwrap() {
        Variable::Bool(assigned) => match parse_expr(&ctx, variables, expr) {
            Ok(value) => match value {
                Value::Bool(b) => add_assumption(
                    ctx,
                    solver,
                    assumptions.clone(),
                    Value::Var(Variable::Bool(
                        assigned._eq(&z3::ast::Bool::from_bool(ctx, b)),
                    )),
                ),
                Value::Var(var) => match var {
                    Variable::Bool(b) => add_assumption(
                        ctx,
                        solver,
                        assumptions.clone(),
                        Value::Var(Variable::Bool(assigned._eq(&b))),
                    ),
                    _ => return Err("Assignment with a value that has wrong type".to_string()),
                },
                _ => return Err("Assignment with a value that has wrong type".to_string()),
            },
            Err(e) => return Err(e),
        },
        Variable::Int(assigned) => match parse_expr(&ctx, variables, expr) {
            Ok(value) => match value {
                Value::Int(b) => add_assumption(
                    ctx,
                    solver,
                    assumptions.clone(),
                    Value::Var(Variable::Bool(
                        assigned._eq(&z3::ast::Int::from_i64(ctx, b)),
                    )),
                ),
                Value::Var(var) => match var {
                    Variable::Int(b) => add_assumption(
                        ctx,
                        solver,
                        assumptions.clone(),
                        Value::Var(Variable::Bool(assigned._eq(&b))),
                    ),
                    _ => return Err("Assignment with a value that has wrong type".to_string()),
                },
                _ => return Err("Assignment with a value that has wrong type".to_string()),
            },
            Err(e) => return Err(e),
        },
    }
}
