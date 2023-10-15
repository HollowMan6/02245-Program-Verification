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
                    let mut counter = HashMap::new();
                    parse_params(&ctx, &mut variables, &mut counter, inputs);
                    parse_params(&ctx, &mut variables, &mut counter, outputs);

                    match parse_specs(
                        &ctx,
                        &mut variables,
                        &mut counter,
                        specifications.clone(),
                        true,
                    ) {
                        Ok(require) => {
                            let mut assumptions: Vec<z3::ast::Bool> = vec![require];
                            match body {
                                Some(b) => {
                                    match parse_body(
                                        &ctx,
                                        &mut variables,
                                        &mut counter,
                                        &solver,
                                        assumptions.clone(),
                                        b,
                                    ) {
                                        Ok(a) => {
                                            assumptions = a;
                                            println!("The body of file {p} parsed successfully");
                                        }
                                        Err(e) => {
                                            println!("{e}");
                                            continue;
                                        }
                                    };
                                }
                                None => {}
                            }
                            match parse_specs(
                                &ctx,
                                &mut variables,
                                &mut counter,
                                specifications,
                                false,
                            ) {
                                Ok(ensure) => {
                                    solver.assert(&ensure);
                                    match add_assumption(
                                        &ctx,
                                        &solver,
                                        assumptions,
                                        Value::Var(Variable::Bool(ensure)),
                                    ) {
                                        Ok(_) => {}
                                        Err(e) => {
                                            println!("{e}");
                                            continue;
                                        }
                                    }
                                }
                                Err(e) => {
                                    println!("{e}");
                                    continue;
                                }
                            };
                        }
                        Err(e) => {
                            println!("{e}");
                            continue;
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
                    let mut counter = HashMap::new();
                    parse_params(&ctx, &mut variables, &mut counter, inputs);

                    match parse_specs(
                        &ctx,
                        &mut variables,
                        &mut counter,
                        specifications.clone(),
                        true,
                    ) {
                        Ok(require) => {
                            let mut assumptions: Vec<z3::ast::Bool> = vec![require];
                            match body {
                                Some(body) => {
                                    // TODO: Add support for functions calling check
                                    let location_msg = format!(
                                        " at location {}-{}",
                                        body.span.start(),
                                        body.span.end()
                                    );
                                    match match parse_expr(
                                        &ctx,
                                        &mut variables,
                                        &mut counter,
                                        "".to_string(),
                                        body,
                                    ) {
                                        Ok((value, _)) => add_assumption(
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
                                                "The function of file {p} parsed successfully {}",
                                                &location_msg
                                            );
                                        }
                                        Err(e) => {
                                            println!("{e} {}", &location_msg);
                                            continue;
                                        }
                                    };
                                }
                                None => {}
                            }
                            match parse_specs(
                                &ctx,
                                &mut variables,
                                &mut counter,
                                specifications,
                                false,
                            ) {
                                Ok(ensure) => {
                                    solver.assert(&ensure);
                                    match add_assumption(
                                        &ctx,
                                        &solver,
                                        assumptions,
                                        Value::Var(Variable::Bool(ensure)),
                                    ) {
                                        Ok(_) => {}
                                        Err(e) => {
                                            println!("{e}");
                                            continue;
                                        }
                                    }
                                }
                                Err(e) => {
                                    println!("{e}");
                                    continue;
                                }
                            };
                        }
                        Err(e) => {
                            println!("{e}");
                            continue;
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
    // None,
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
        // Value::None => None,
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
    counter: &mut HashMap<String, i64>,
    name: String,
    ty: ast::Type,
) {
    let variable = match ty {
        ast::Type::Bool => Variable::Bool(z3::ast::Bool::new_const(&ctx, name.clone() + "0")),
        ast::Type::Int => Variable::Int(z3::ast::Int::new_const(&ctx, name.clone() + "0")),
    };
    variables.insert(name.clone() + "0", variable);
    counter.insert(name, 0);
}

fn fresh_variable<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    name: String,
) -> Variable<'a> {
    let num = counter.get(&name).unwrap();
    let new_name = name.clone() + &(num + 1).to_string();
    let var = match *(variables.get(&(name.clone() + &num.to_string())).unwrap()) {
        Variable::Bool(_) => Variable::Bool(z3::ast::Bool::new_const(&ctx, new_name.clone())),
        Variable::Int(_) => Variable::Int(z3::ast::Int::new_const(&ctx, new_name.clone())),
    };
    variables.insert(new_name, var.clone());
    counter.insert(name, num + 1);
    var
}

fn parse_params<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    params: Vec<ast::Var>,
) {
    for param in params {
        let ast::Var { name, ty } = param;
        parse_type(&ctx, variables, counter, name.text, ty);
    }
}

// Parse specifications
fn parse_specs<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    specs: Vec<ast::Specification>,
    requires: bool,
) -> Result<z3::ast::Bool<'a>, String> {
    let mut conditions = Vec::new();
    for spec in specs {
        match spec {
            ast::Specification::Ensures(e) => {
                if requires {
                    continue;
                }
                match parse_expr(&ctx, variables, counter, "".to_string(), e) {
                    Ok((value, _)) => match value {
                        Value::Bool(b) => conditions.push(z3::ast::Bool::from_bool(ctx, b)),
                        Value::Var(var) => match var {
                            Variable::Bool(b) => conditions.push(b),
                            _ => return Err("Ensures with a value that has wrong type".to_string()),
                        },
                        _ => return Err("Ensures with a value that has wrong type".to_string()),
                    },
                    Err(e) => return Err(e),
                }
            }
            ast::Specification::Requires(r) => {
                if !requires {
                    continue;
                }
                match parse_expr(&ctx, variables, counter, "".to_string(), r) {
                    Ok((value, _)) => match value {
                        Value::Bool(b) => conditions.push(z3::ast::Bool::from_bool(ctx, b)),
                        Value::Var(var) => match var {
                            Variable::Bool(b) => conditions.push(b),
                            _ => {
                                return Err("Requires with a value that has wrong type".to_string())
                            }
                        },
                        _ => return Err("Requires with a value that has wrong type".to_string()),
                    },
                    Err(e) => return Err(e),
                }
            }
        };
    }
    let mut condition = match conditions.pop() {
        Some(r) => r,
        None => z3::ast::Bool::from_bool(ctx, true),
    };
    while conditions.len() > 0 {
        condition = match conditions.pop() {
            Some(r) => z3::ast::Bool::and(ctx, &[&condition, &r]),
            None => condition,
        };
    }
    Ok(condition)
}

fn parse_expr<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    assgining_var: String,
    expr: ast::Expr,
) -> Result<(Value<'a>, bool), String> {
    let kind = expr.kind;
    match parse_expr_kind(&ctx, variables, counter, assgining_var, kind) {
        Ok((value, b)) => Ok((value, b)),
        Err(e) => Err(e),
    }
}

fn parse_expr_kind<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    assgining_var: String,
    expr_kind: Box<ast::ExprKind>,
) -> Result<(Value<'a>, bool), String> {
    match *expr_kind {
        ast::ExprKind::Boolean(b) => Ok((Value::Bool(b), false)),
        ast::ExprKind::Integer(i) => Ok((Value::Int(i.parse().unwrap()), false)),
        ast::ExprKind::Var(ident) => Ok((
            Value::Var(
                variables
                    .get(&(ident.text.clone() + &counter.get(&ident.text).unwrap().to_string()))
                    .unwrap()
                    .clone(),
            ),
            ident.text == assgining_var.clone(),
        )),
        // TODO: handle result and call
        ast::ExprKind::Result => Ok((Value::Bool(true), false)),
        ast::ExprKind::Call(ident, exprs) => {
            println!("Call: {}", ident.text);
            for expr in exprs {
                let _ = parse_expr(&ctx, variables, counter, assgining_var.clone(), expr);
            }
            Ok((
                Value::Var(
                    variables
                        .get(&(ident.text.clone() + &counter.get(&ident.text).unwrap().to_string()))
                        .unwrap()
                        .clone(),
                ),
                ident.text == assgining_var,
            ))
        }
        ast::ExprKind::Unary(uop, expr) => {
            match parse_expr(&ctx, variables, counter, assgining_var, expr) {
                Ok((value, fresh)) => match uop {
                    ast::UOp::Minus => match value {
                        Value::Int(i) => Ok((Value::Int(-i), fresh)),
                        Value::Var(var) => match var {
                            Variable::Int(i) => {
                                Ok((Value::Var(Variable::Int(i.unary_minus())), fresh))
                            }
                            _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                        },
                        _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                    },
                    ast::UOp::Not => match value {
                        Value::Bool(i) => Ok((Value::Bool(!i), fresh)),
                        Value::Var(var) => match var {
                            Variable::Bool(i) => Ok((Value::Var(Variable::Bool(i.not())), fresh)),
                            _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                        },
                        _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                    },
                },
                Err(e) => Err(e),
            }
        }
        ast::ExprKind::Binary(expr1, op, expr2) => {
            // Give some example for this you have in mind?
            match parse_expr(&ctx, variables, counter, assgining_var.clone(), expr1) {
                Ok((value1, fresh1)) => {
                    match parse_expr(&ctx, variables, counter, assgining_var, expr2) {
                        Ok((value2, fresh2)) => match op {
                            ast::Op::And => match value1 {
                                Value::Bool(var1) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok((Value::Bool(var1 && var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i) => Ok((
                                            Value::Var(Variable::Bool(z3::ast::Bool::and(
                                                ctx,
                                                &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("&& with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("&& with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Bool(i) => match value2 {
                                        Value::Bool(var2) => Ok((
                                            Value::Var(Variable::Bool(z3::ast::Bool::and(
                                                ctx,
                                                &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::and(
                                                        ctx,
                                                        &[&i, &i2],
                                                    ))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("&& with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("&& with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("&& with a value that has wrong type".to_string()),
                                },
                                _ => Err("&& with a value that has wrong type".to_string()),
                            },
                            ast::Op::Divide => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Int(var1 / var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Int(
                                                z3::ast::Int::from_i64(ctx, var1).div(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("/ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("/ with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Int(
                                                i.div(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Int(i.div(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("/ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("/ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("/ with a value that has wrong type".to_string()),
                                },
                                _ => Err("/ with a value that has wrong type".to_string()),
                            },
                            ast::Op::Eq => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 == var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1)._eq(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                Value::Bool(var1) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok((Value::Bool(var1 == var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Bool::from_bool(ctx, var1)._eq(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("== with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i._eq(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    Variable::Bool(i) => match value2 {
                                        Value::Bool(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i._eq(&z3::ast::Bool::from_bool(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    // _ => Err("== with a value that has wrong type".to_string()),
                                },
                                // _ => Err("== with a value that has wrong type".to_string()),
                            },
                            ast::Op::Geq => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 >= var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1).ge(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err(">= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err(">= with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i.ge(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.ge(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err(">= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err(">= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err(">= with a value that has wrong type".to_string()),
                                },
                                _ => Err(">= with a value that has wrong type".to_string()),
                            },
                            ast::Op::Gt => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 > var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1).gt(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("> with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("> with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i.gt(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.gt(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("> with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("> with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("> with a value that has wrong type".to_string()),
                                },
                                _ => Err("> with a value that has wrong type".to_string()),
                            },
                            ast::Op::Implies => match value1 {
                                Value::Bool(var1) => match value2 {
                                    Value::Bool(var2) => Ok((
                                        Value::Var(Variable::Bool(
                                            z3::ast::Bool::from_bool(ctx, var1)
                                                .implies(&z3::ast::Bool::from_bool(ctx, var2)),
                                        )),
                                        fresh1 || fresh2,
                                    )),
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Bool::from_bool(ctx, var1).implies(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => {
                                            Err("==> with a value that has wrong type".to_string())
                                        }
                                    },
                                    _ => Err("==> with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Bool(i) => match value2 {
                                        Value::Bool(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i.implies(&z3::ast::Bool::from_bool(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.implies(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("==> with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => {
                                            Err("==> with a value that has wrong type".to_string())
                                        }
                                    },
                                    _ => Err("==> with a value that has wrong type".to_string()),
                                },
                                _ => Err("==> with a value that has wrong type".to_string()),
                            },
                            ast::Op::Leq => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 <= var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1).le(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("<= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("<= with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i.le(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.le(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("<= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("<= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("<= with a value that has wrong type".to_string()),
                                },
                                _ => Err("<= with a value that has wrong type".to_string()),
                            },
                            ast::Op::Lt => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 < var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1).lt(&i),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("< with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("< with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i.lt(&z3::ast::Int::from_i64(ctx, var2)),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.lt(&i2))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("< with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("< with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("< with a value that has wrong type".to_string()),
                                },
                                _ => Err("< with a value that has wrong type".to_string()),
                            },
                            ast::Op::Minus => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Int(var1 - var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::sub(
                                                ctx,
                                                &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("- with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("- with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::sub(
                                                ctx,
                                                &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::sub(
                                                        ctx,
                                                        &[&i, &i2],
                                                    ))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("- with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("- with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("- with a value that has wrong type".to_string()),
                                },
                                _ => Err("- with a value that has wrong type".to_string()),
                            },
                            ast::Op::Neq => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Bool(var1 != var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Int::from_i64(ctx, var1)._eq(&i).not(),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                Value::Bool(var1) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok((Value::Bool(var1 != var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i) => Ok((
                                            Value::Var(Variable::Bool(
                                                z3::ast::Bool::from_bool(ctx, var1)._eq(&i).not(),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i._eq(&z3::ast::Int::from_i64(ctx, var2)).not(),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2).not())),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("!= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    Variable::Bool(i) => match value2 {
                                        Value::Bool(var2) => Ok((
                                            Value::Var(Variable::Bool(
                                                i._eq(&z3::ast::Bool::from_bool(ctx, var2)).not(),
                                            )),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2).not())),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("!= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    // _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                // _ => Err("!= with a value that has wrong type".to_string()),
                            },
                            ast::Op::Or => match value1 {
                                Value::Bool(var1) => match value2 {
                                    Value::Bool(var2) => {
                                        Ok((Value::Bool(var1 || var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Bool(i) => Ok((
                                            Value::Var(Variable::Bool(z3::ast::Bool::or(
                                                ctx,
                                                &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("|| with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("|| with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Bool(i) => match value2 {
                                        Value::Bool(var2) => Ok((
                                            Value::Var(Variable::Bool(z3::ast::Bool::or(
                                                ctx,
                                                &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::or(
                                                        ctx,
                                                        &[&i, &i2],
                                                    ))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("|| with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("|| with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("|| with a value that has wrong type".to_string()),
                                },
                                _ => Err("|| with a value that has wrong type".to_string()),
                            },
                            ast::Op::Plus => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Int(var1 + var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::add(
                                                ctx,
                                                &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("+ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("+ with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::add(
                                                ctx,
                                                &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::add(
                                                        ctx,
                                                        &[&i, &i2],
                                                    ))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("+ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("+ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("+ with a value that has wrong type".to_string()),
                                },
                                _ => Err("+ with a value that has wrong type".to_string()),
                            },
                            ast::Op::Times => match value1 {
                                Value::Int(var1) => match value2 {
                                    Value::Int(var2) => {
                                        Ok((Value::Int(var1 * var2), fresh1 || fresh2))
                                    }
                                    Value::Var(var2) => match var2 {
                                        Variable::Int(i) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::mul(
                                                ctx,
                                                &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        _ => Err("* with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("* with a value that has wrong type".to_string()),
                                },
                                Value::Var(var) => match var {
                                    Variable::Int(i) => match value2 {
                                        Value::Int(var2) => Ok((
                                            Value::Var(Variable::Int(z3::ast::Int::mul(
                                                ctx,
                                                &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                            ))),
                                            fresh1 || fresh2,
                                        )),
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::mul(
                                                        ctx,
                                                        &[&i, &i2],
                                                    ))),
                                                    fresh1 || fresh2,
                                                )),
                                                _ => Err("* with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("* with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("* with a value that has wrong type".to_string()),
                                },
                                _ => Err("* with a value that has wrong type".to_string()),
                            },
                        },
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        }
        ast::ExprKind::Quantification(quantifier, var, expr) => {
            let ast::Var { name, ty } = var;
            println!("Var: {}", name.text);
            parse_type(&ctx, variables, counter, name.text.clone(), ty);
            match parse_expr(&ctx, variables, counter, assgining_var, expr) {
                Ok((value, fresh)) => {
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
                            match variables
                                .get(
                                    &(name.text.clone()
                                        + &counter.get(&name.text).unwrap().to_string()),
                                )
                                .unwrap()
                                .clone()
                            {
                                Variable::Bool(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::forall_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    fresh,
                                )),
                                Variable::Int(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::forall_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    fresh,
                                )),
                            }
                        }
                        ast::Quantifier::Exists => {
                            match variables
                                .get(
                                    &(name.text.clone()
                                        + &counter.get(&name.text).unwrap().to_string()),
                                )
                                .unwrap()
                                .clone()
                            {
                                Variable::Bool(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::exists_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    fresh,
                                )),
                                Variable::Int(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::exists_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    fresh,
                                )),
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
    counter: &mut HashMap<String, i64>,
    solver: &z3::Solver,
    assumptions: Vec<z3::ast::Bool<'a>>,
    body: ast::Body,
) -> Result<Vec<z3::ast::Bool<'a>>, String> {
    let mut assumptions = assumptions;
    for stmt in body.statements {
        let mut location_msg = "".to_string();
        assumptions = match match stmt {
            ast::Statement::Var(var, expr) => {
                let ast::Var { name, ty } = var;
                parse_type(&ctx, variables, counter, name.text.clone(), ty);
                match expr {
                    Some(expr) => {
                        parse_assignment(ctx, variables, counter, solver, assumptions, name, expr)
                    }
                    None => Ok(assumptions),
                }
            }
            ast::Statement::Assert(expr) => {
                location_msg = format!(" at location {}-{}", expr.span.start(), expr.span.end());
                match parse_expr(&ctx, variables, counter, "".to_string(), expr) {
                    Ok((value, _)) => match value.clone() {
                        Value::Bool(b) => {
                            solver.assert(&z3::ast::Bool::from_bool(ctx, b));
                            add_assumption(ctx, solver, assumptions, value.clone())
                        }
                        Value::Var(var) => match var {
                            Variable::Bool(b) => {
                                solver.assert(&b);
                                add_assumption(ctx, solver, assumptions, value)
                            }
                            _ => {
                                return Err("Assert with a value that has wrong type".to_string()
                                    + &location_msg)
                            }
                        },
                        _ => {
                            return Err("Assert with a value that has wrong type".to_string()
                                + &location_msg)
                        }
                    },
                    Err(e) => return Err(e + &location_msg),
                }
            }
            ast::Statement::Assume(expr) => {
                location_msg = format!(" at location {}-{}", expr.span.start(), expr.span.end());
                match parse_expr(&ctx, variables, counter, "".to_string(), expr) {
                    Ok((value, _)) => match value.clone() {
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
                            _ => {
                                return Err("Assume with a value that has wrong type".to_string()
                                    + &location_msg)
                            }
                        },
                        _ => {
                            return Err("Assume with a value that has wrong type".to_string()
                                + &location_msg)
                        }
                    },
                    Err(e) => return Err(e + &location_msg),
                }
            }
            ast::Statement::Assignment(ident, expr) => {
                parse_assignment(ctx, variables, counter, solver, assumptions, ident, expr)
            }
            ast::Statement::MethodAssignment(idents, ident, exprs) => {
                // TODO: Support method assignment
                println!("MethodAssignment: {}", ident.text);
                for ident in idents {
                    println!("Var: {}", ident.text);
                }
                for expr in exprs {
                    let location_msg =
                        format!(" at location {}-{}", expr.span.start(), expr.span.end());
                    match parse_expr(&ctx, variables, counter, "".to_string(), expr) {
                        Ok(_) => {}
                        Err(e) => return Err(e + &location_msg),
                    };
                }
                Ok(assumptions)
            }
            ast::Statement::If(expr, body, body_opt) => {
                location_msg = format!(" at location {}-{}", expr.span.start(), expr.span.end());
                match parse_expr(&ctx, variables, counter, "".to_string(), expr) {
                    Ok((value, _)) => {
                        let mut if_branch_counter = counter.clone();
                        let mut assumptions_if =
                            match add_assumption(ctx, solver, assumptions.clone(), value.clone()) {
                                Ok(if_ass) => {
                                    match parse_body(
                                        &ctx,
                                        variables,
                                        &mut if_branch_counter,
                                        solver,
                                        if_ass,
                                        body,
                                    ) {
                                        Ok(a) => a,
                                        Err(e) => return Err(e + &location_msg),
                                    }
                                }
                                Err(e) => return Err(e + &location_msg),
                            };
                        let mut else_branch_counter = counter.clone();
                        match body_opt {
                            Some(body) => {
                                match match value {
                                    Value::Bool(b) => Ok(Value::Bool(!b)),
                                    Value::Var(var) => match var {
                                        Variable::Bool(b) => {
                                            Ok(Value::Var(Variable::Bool(b.not())))
                                        }
                                        _ => Err("if condition with a value that has wrong type"
                                            .to_string()
                                            + &location_msg),
                                    },
                                    _ => Err("if condition with a value that has wrong type"
                                        .to_string()
                                        + &location_msg),
                                } {
                                    Ok(else_ass) => {
                                        match add_assumption(ctx, solver, assumptions, else_ass) {
                                            Ok(else_assumptions) => {
                                                match parse_body(
                                                    &ctx,
                                                    variables,
                                                    &mut else_branch_counter,
                                                    solver,
                                                    else_assumptions,
                                                    body,
                                                ) {
                                                    Ok(final_ass) => {
                                                        let mut final_ass = final_ass;
                                                        for key in counter.clone().keys() {
                                                            let if_branch =
                                                                if_branch_counter.get(key).unwrap();
                                                            let else_branch = else_branch_counter
                                                                .get(key)
                                                                .unwrap();
                                                            let if_branch_var = variables
                                                                .get(
                                                                    &(key.clone()
                                                                        + &if_branch.to_string()),
                                                                )
                                                                .unwrap();
                                                            let else_branch_var = variables
                                                                .get(
                                                                    &(key.clone()
                                                                        + &else_branch.to_string()),
                                                                )
                                                                .unwrap();
                                                            let mut num = if_branch.clone();
                                                            if if_branch > else_branch {
                                                                final_ass = match add_assumption(
                                                                ctx,
                                                                solver,
                                                                final_ass,
                                                                match if_branch_var {
                                                                    Variable::Bool(var1) => match else_branch_var {
                                                                        Variable::Bool(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                                                                        _ => return Err("Unmatched var in fresh var assignment".to_string() + &location_msg)
                                                                    }
                                                                    Variable::Int(var1) => match else_branch_var {
                                                                        Variable::Int(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                                                                        _ => return Err("Unmatched var in fresh var assignment".to_string() + &location_msg)
                                                                    }
                                                                },
                                                            ) {
                                                                Ok(a) => a,
                                                                Err(e) => return Err(e + &location_msg),
                                                            }
                                                            } else if else_branch > if_branch {
                                                                num = else_branch.clone();
                                                                assumptions_if = match add_assumption(
                                                                    ctx,
                                                                    solver,
                                                                    assumptions_if,
                                                                    match else_branch_var {
                                                                        Variable::Bool(var1) => match if_branch_var {
                                                                            Variable::Bool(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                                                                            _ => return Err("Unmatched var in fresh var assignment".to_string() + &location_msg)
                                                                        }
                                                                        Variable::Int(var1) => match if_branch_var {
                                                                            Variable::Int(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                                                                            _ => return Err("Unmatched var in fresh var assignment".to_string() + &location_msg)
                                                                        }
                                                                    },
                                                                ) {
                                                                    Ok(a) => a,
                                                                    Err(e) => return Err(e + &location_msg),
                                                                }
                                                            }
                                                            counter.insert(key.clone(), num);
                                                        }
                                                        Ok(vec![assumptions_if.clone(), final_ass]
                                                            .concat())
                                                    }
                                                    Err(e) => Err(e + &location_msg),
                                                }
                                            }
                                            Err(e) => Err(e + &location_msg),
                                        }
                                    }
                                    Err(e) => Err(e + &location_msg),
                                }
                            }
                            None => Ok(assumptions_if),
                        }
                    }
                    Err(e) => return Err(e + &location_msg),
                }
            }
            ast::Statement::While {
                condition,
                invariants: _,
                body: _,
            } => {
                // TODO: Support while, now we just skip while block
                location_msg = format!(
                    " at location {}-{}",
                    condition.span.start(),
                    condition.span.end()
                );
                match parse_expr(&ctx, variables, counter, "".to_string(), condition) {
                    Ok(_) => {
                        break;
                        // for invariant in invariants {
                        //     match parse_expr(&ctx, variables, counter, "".to_string(), invariant) {
                        //         Ok(_) => {}
                        //         Err(e) => return Err(e + &location_msg),
                        //     };
                        // }
                        // parse_body(&ctx, variables, counter, solver, assumptions.clone(), body)
                    }
                    Err(e) => return Err(e + &location_msg),
                }
            }
        } {
            Ok(a) => a,
            Err(e) => return Err(e + &location_msg),
        }
    }
    Ok(assumptions)
}

fn parse_assignment<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    solver: &z3::Solver,
    assumptions: Vec<z3::ast::Bool<'a>>,
    ident: ast::Ident,
    expr: ast::Expr,
) -> Result<Vec<z3::ast::Bool<'a>>, String> {
    let location_msg = format!(" at location {}-{}", expr.span.start(), expr.span.end());
    match variables
        .clone()
        .get(&(ident.text.clone() + &counter.get(&ident.text.clone()).unwrap().to_string()))
        .unwrap()
    {
        Variable::Bool(assigned) => {
            match parse_expr(&ctx, variables, counter, ident.text.clone(), expr) {
                Ok((value, fresh)) => {
                    let mut assigned = assigned.clone();
                    if fresh {
                        assigned = match fresh_variable(ctx, variables, counter, ident.text) {
                            Variable::Bool(b) => b,
                            _ => {
                                return Err("Assignment with a fresh value that has wrong type"
                                    .to_string()
                                    + &location_msg)
                            }
                        }
                    }
                    match value {
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
                            _ => {
                                return Err("Assignment with a value that has wrong type"
                                    .to_string()
                                    + &location_msg)
                            }
                        },
                        _ => {
                            return Err("Assignment with a value that has wrong type".to_string()
                                + &location_msg)
                        }
                    }
                }
                Err(e) => return Err(e + &location_msg),
            }
        }
        Variable::Int(assigned) => {
            match parse_expr(&ctx, variables, counter, ident.text.clone(), expr) {
                Ok((value, fresh)) => {
                    let mut assigned = assigned.clone();
                    if fresh {
                        assigned = match fresh_variable(ctx, variables, counter, ident.text) {
                            Variable::Int(i) => i,
                            _ => {
                                return Err("Assignment with a fresh value that has wrong type"
                                    .to_string()
                                    + &location_msg)
                            }
                        }
                    }
                    match value {
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
                            _ => {
                                return Err("Assignment with a value that has wrong type"
                                    .to_string()
                                    + &location_msg)
                            }
                        },
                        _ => {
                            return Err("Assignment with a value that has wrong type".to_string()
                                + &location_msg)
                        }
                    }
                }
                Err(e) => return Err(e + &location_msg),
            }
        }
    }
}
