use miette::{miette, LabeledSpan, Report, Result};
use std::{
    collections::{HashMap, HashSet},
    fs,
};
pub use syntax::ast;
use z3::ast::Ast;

const DEBUG: bool = true;

fn main() -> Result<()> {
    // Parsing
    for p in std::env::args().skip(1) {
        let doc_ast = syntax::parse_file(p.clone())?;
        let code = fs::read_to_string(p.clone()).unwrap();
        let mut global_inputs: HashMap<String, Vec<ast::Var>> = HashMap::new();
        let mut global_outputs: HashMap<String, Vec<ast::Var>> = HashMap::new();
        let mut global_ensures: HashMap<String, Vec<ast::Expr>> = HashMap::new();
        let mut global_requires: HashMap<String, Vec<ast::Expr>> = HashMap::new();
        let mut global_functions: HashMap<String, Option<ast::Expr>> = HashMap::new();
        // First round, collect all methods signatures and functions
        for item in doc_ast.items.clone() {
            match item {
                ast::DocumentItem::Method(method) => {
                    let ast::Method {
                        name,
                        inputs,
                        outputs,
                        specifications,
                        body: _,
                    } = method;
                    global_inputs.insert(name.text.clone(), inputs.clone());
                    global_outputs.insert(name.text.clone(), outputs.clone());
                    let mut ensures = Vec::new();
                    let mut requires = Vec::new();
                    for spec in specifications {
                        match spec {
                            ast::Specification::Ensures(e) => ensures.push(e),
                            ast::Specification::Requires(r) => requires.push(r),
                        }
                    }
                    global_ensures.insert(name.text.clone(), ensures);
                    global_requires.insert(name.text.clone(), requires);
                }
                ast::DocumentItem::Function(function) => {
                    let ast::Function {
                        name,
                        inputs,
                        ret_ty: _,
                        specifications,
                        body,
                    } = function;
                    global_inputs.insert(name.text.clone(), inputs.clone());
                    let mut ensures = Vec::new();
                    let mut requires = Vec::new();
                    for spec in specifications {
                        match spec {
                            ast::Specification::Ensures(e) => ensures.push(e),
                            ast::Specification::Requires(r) => requires.push(r),
                        }
                    }
                    global_ensures.insert(name.text.clone(), ensures);
                    global_requires.insert(name.text.clone(), requires);
                    global_functions.insert(name.text.clone(), body.clone());
                }
            }
        }
        // Second round, parse all methods
        for item in doc_ast.items {
            let cfg = z3::Config::new();
            let ctx = z3::Context::new(&cfg);
            let solver = z3::Solver::new(&ctx);
            match item {
                ast::DocumentItem::Method(method) => {
                    // Access fields of method
                    let ast::Method {
                        name,
                        inputs,
                        outputs,
                        specifications,
                        body,
                    } = method;

                    // Define variables hashmap and store it in context
                    let mut variables = HashMap::new();
                    let mut counter = HashMap::new();
                    parse_params(&ctx, &mut variables, &mut counter, inputs, "".to_string());
                    parse_params(&ctx, &mut variables, &mut counter, outputs, "".to_string());

                    let mut assumptions = vec![vec![]];
                    match parse_specs(
                        &ctx,
                        &mut variables,
                        &mut counter,
                        &solver,
                        assumptions,
                        specifications.clone(),
                        true,
                        code.clone(),
                        p.clone(),
                        global_inputs.clone(),
                        global_outputs.clone(),
                        global_ensures.clone(),
                        global_requires.clone(),
                        global_functions.clone(),
                        "".to_string(),
                    ) {
                        Ok((require, a)) => match require {
                            Some(req) => {
                                match add_assumption(
                                    &ctx,
                                    &solver,
                                    a,
                                    Value::Var(Variable::Bool(req)),
                                    (name.span.start(), name.span.end()),
                                    code.clone(),
                                    p.clone(),
                                ) {
                                    Ok(ass) => {
                                        assumptions = ass;
                                    }
                                    Err(e) => {
                                        println!(
                                            "{:?}",
                                            generate_error(
                                                Wrong {
                                                    msg: e,
                                                    span: (name.span.start(), name.span.end())
                                                },
                                                code.clone(),
                                                p.clone()
                                            )
                                        );
                                        continue;
                                    }
                                }
                                match body {
                                    Some(b) => {
                                        match parse_body(
                                            &ctx,
                                            &mut variables,
                                            &mut counter,
                                            &solver,
                                            assumptions.clone(),
                                            b.clone(),
                                            code.clone(),
                                            p.clone(),
                                            global_inputs.clone(),
                                            global_outputs.clone(),
                                            global_ensures.clone(),
                                            global_requires.clone(),
                                            global_functions.clone(),
                                            "".to_string(),
                                        ) {
                                            Ok(a) => {
                                                assumptions = a;
                                            }
                                            Err(e) => {
                                                println!(
                                                    "{:?}",
                                                    generate_error(e, code.clone(), p.clone())
                                                );
                                                continue;
                                            }
                                        };
                                        let (total_correct, location) =
                                            check_method_total_correctness(b, name.text.clone());
                                        if !total_correct {
                                            println!(
                                                    "{:?}",
                                                    generate_error(
                                                        Wrong {
                                                            msg: "Warning: Calling method now will likely cause infinite stack (not totally correct)".to_string(),
                                                            span: location
                                                        },
                                                        code.clone(),
                                                        p.clone()
                                                    )
                                                );
                                        }
                                    }
                                    None => {
                                        if DEBUG {
                                            println!(
                                                "Skip checking method {} at file {} as there's no body",
                                                name.text, p
                                            );
                                        }
                                        continue;
                                    }
                                }
                                assumptions = match parse_specs(
                                    &ctx,
                                    &mut variables,
                                    &mut counter,
                                    &solver,
                                    assumptions.clone(),
                                    specifications,
                                    false,
                                    code.clone(),
                                    p.clone(),
                                    global_inputs.clone(),
                                    global_outputs.clone(),
                                    global_ensures.clone(),
                                    global_requires.clone(),
                                    global_functions.clone(),
                                    "".to_string(),
                                ) {
                                    Ok(_) => assumptions,
                                    Err(e) => {
                                        println!(
                                            "{:?}",
                                            generate_error(e, code.clone(), p.clone())
                                        );
                                        continue;
                                    }
                                };
                                if DEBUG {
                                    println!(
                                        "Parsing method {} in file {} complete! Translated Z3 AST is:",
                                        name.text, p
                                    );
                                    dbg!(assumptions);
                                }
                            }
                            None => {
                                println!("Skip parsing method {} at file {} as requires conditions are not valid", name.text, p);
                                continue;
                            }
                        },
                        Err(e) => {
                            println!("{:?}", generate_error(e, code.clone(), p.clone()));
                            continue;
                        }
                    };
                }
                ast::DocumentItem::Function(function) => {
                    // Access fields of function
                    let ast::Function {
                        name,
                        inputs,
                        ret_ty: _,
                        specifications,
                        body,
                    } = function;

                    // Define variables hashmap and store it in context
                    let mut variables: HashMap<String, Variable> = HashMap::new();
                    let mut counter = HashMap::new();
                    parse_params(&ctx, &mut variables, &mut counter, inputs, "".to_string());

                    let mut assumptions = vec![vec![]];
                    match parse_specs(
                        &ctx,
                        &mut variables,
                        &mut counter,
                        &solver,
                        assumptions,
                        specifications.clone(),
                        true,
                        code.clone(),
                        p.clone(),
                        global_inputs.clone(),
                        global_outputs.clone(),
                        global_ensures.clone(),
                        global_requires.clone(),
                        global_functions.clone(),
                        "".to_string(),
                    ) {
                        Ok((require, a)) => {
                            assumptions = a;
                            match require {
                                Some(req) => {
                                    match add_assumption(
                                        &ctx,
                                        &solver,
                                        assumptions,
                                        Value::Var(Variable::Bool(req)),
                                        (name.span.start(), name.span.end()),
                                        code.clone(),
                                        p.clone(),
                                    ) {
                                        Ok(ass) => {
                                            assumptions = ass;
                                        }
                                        Err(e) => {
                                            println!(
                                                "{:?}",
                                                generate_error(
                                                    Wrong {
                                                        msg: e,
                                                        span: (name.span.start(), name.span.end())
                                                    },
                                                    code.clone(),
                                                    p.clone()
                                                )
                                            );
                                            continue;
                                        }
                                    }
                                    match body {
                                        Some(body) => {
                                            let location = (
                                                body.clone().span.start(),
                                                body.clone().span.end(),
                                            );
                                            match match parse_expr(
                                                &ctx,
                                                &mut variables,
                                                &mut counter,
                                                body,
                                                &solver,
                                                assumptions.clone(),
                                                code.clone(),
                                                p.clone(),
                                                global_inputs.clone(),
                                                global_outputs.clone(),
                                                global_ensures.clone(),
                                                global_requires.clone(),
                                                global_functions.clone(),
                                                "".to_string(),
                                            ) {
                                                Ok((_, a)) => {
                                                    assumptions = a;
                                                    // add_assumption(&ctx, &solver, assumptions.clone(), value, location, code.clone(), p.clone())
                                                    Ok(assumptions)
                                                }
                                                Err(e) => {
                                                    println!(
                                                        "{:?}",
                                                        generate_error(
                                                            Wrong {
                                                                msg: e,
                                                                span: location
                                                            },
                                                            code.clone(),
                                                            p.clone()
                                                        )
                                                    );
                                                    continue;
                                                }
                                            } {
                                                Ok(a) => {
                                                    assumptions = a;
                                                }
                                                Err(e) => {
                                                    println!(
                                                        "{:?}",
                                                        generate_error(
                                                            Wrong {
                                                                msg: e,
                                                                span: location
                                                            },
                                                            code.clone(),
                                                            p.clone()
                                                        )
                                                    );
                                                    continue;
                                                }
                                            };
                                        }
                                        None => {}
                                    }
                                    assumptions = match parse_specs(
                                        &ctx,
                                        &mut variables,
                                        &mut counter,
                                        &solver,
                                        assumptions.clone(),
                                        specifications,
                                        false,
                                        code.clone(),
                                        p.clone(),
                                        global_inputs.clone(),
                                        global_outputs.clone(),
                                        global_ensures.clone(),
                                        global_requires.clone(),
                                        global_functions.clone(),
                                        "".to_string(),
                                    ) {
                                        Ok((ensure, a)) => {
                                            assumptions = a;
                                            match ensure {
                                                Some(en) => match add_assumption(
                                                    &ctx,
                                                    &solver,
                                                    assumptions.clone(),
                                                    Value::Var(Variable::Bool(en)),
                                                    (name.span.start(), name.span.end()),
                                                    code.clone(),
                                                    p.clone(),
                                                ) {
                                                    Ok(a) => a,
                                                    Err(e) => {
                                                        println!("{e} at ensures in file {p}");
                                                        continue;
                                                    }
                                                },
                                                None => assumptions,
                                            }
                                        }
                                        Err(e) => {
                                            println!(
                                                "{:?}",
                                                generate_error(e, code.clone(), p.clone())
                                            );
                                            continue;
                                        }
                                    };
                                    if DEBUG {
                                        println!(
                                            "Parsing function {} in file {} complete! Translated Z3 AST is:",
                                            name.text, p
                                        );
                                        dbg!(assumptions);
                                    }
                                }
                                None => {
                                    println!("Skip parsing function {} at file {} as requires conditions are not valid", name.text, p);
                                    continue;
                                }
                            }
                        }
                        Err(e) => {
                            println!("{:?}", generate_error(e, code.clone(), p.clone()));
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

struct Wrong {
    msg: String,
    span: (usize, usize),
}

fn generate_error(Wrong { msg, span }: Wrong, file: String, path: String) -> Report {
    miette!(
        labels = vec![LabeledSpan::at(span.0..span.1, msg)],
        help = "Fix this and try again!",
        "An error occurred while checking {}:",
        path
    )
    .with_source_code(file)
}

fn assert<'a>(
    ctx: &'a z3::Context,
    solver: &z3::Solver,
    assumptions: &[Vec<z3::ast::Bool>],
    assertion: z3::ast::Bool<'a>,
) -> Result<(), String> {
    for assumption in assumptions {
        let mut condition = if assumption.len() > 0 {
            assumption[0].clone()
        } else {
            z3::ast::Bool::from_bool(ctx, true)
        };
        for r in assumption.iter().skip(1) {
            condition = z3::ast::Bool::and(ctx, &[&condition, r]);
        }
        let to_check = [z3::ast::Bool::and(ctx, &[&condition])
            .implies(&assertion)
            .not()];
        if DEBUG {
            dbg!(&to_check);
        }
        match solver.check_assumptions(&to_check) {
            z3::SatResult::Unsat => {
                if DEBUG {
                    // for unsat in solver.get_unsat_core() {
                    //     dbg!(unsat);
                    // }
                    println!("OK");
                }
            }
            z3::SatResult::Unknown => {
                if let Some(_) = solver.get_model() {
                    continue;
                }
                return Err(
                    " + This assertion may be unsatisfiable but couldn't extract a model"
                        .to_string(),
                );
            }
            z3::SatResult::Sat => {
                return Err(" + This assertion is unsatisfiable".to_string());
            }
        };
    }
    Ok(())
}

fn add_assumption<'a>(
    ctx: &'a z3::Context,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    assumption: Value<'a>,
    location: (usize, usize),
    code: String,
    path: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, String> {
    let mut new_assumptions: Vec<Vec<z3::ast::Bool<'a>>> = Vec::new();
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
            for mut ass in assumptions {
                ass.push(a.clone());
                new_assumptions.push(ass)
            }
        }
        None => new_assumptions = assumptions,
    }
    let mut to_remove: HashSet<usize> = HashSet::new();
    // Test to check if we have any contradictory assumptions
    for (index, ass) in new_assumptions.iter().enumerate() {
        match assert(
            ctx,
            solver,
            &[ass.clone()],
            z3::ast::Bool::from_bool(ctx, false),
        ) {
            Ok(_) => {
                to_remove.insert(index);
                println!(
                    "{:?}",
                    generate_error(
                        Wrong {
                            msg: "Warning: This assumption causes contradiction in one of the branch, dropping that branch now".to_string(),
                            span: location,
                        },
                        code.clone(),
                        path.clone()
                    )
                );
            }
            Err(_) => {
                continue;
            }
        }
    }
    let mut final_assumptions: Vec<Vec<z3::ast::Bool<'a>>> = Vec::new();
    for (index, ass) in new_assumptions.iter().enumerate() {
        if !to_remove.contains(&index) {
            final_assumptions.push(ass.clone())
        }
    }
    Ok(final_assumptions)
    // if final_assumptions.len() > 0 {
    //     Ok(final_assumptions)
    // } else {
    //     Err("Stop checking now as no valid asumptions are available".to_string())
    // }
}

fn parse_type<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    name: String,
    ty: ast::Type,
    prefix: String,
) {
    let variable = match ty {
        ast::Type::Bool => Variable::Bool(z3::ast::Bool::new_const(
            &ctx,
            prefix.clone() + &name.clone() + "0",
        )),
        ast::Type::Int => Variable::Int(z3::ast::Int::new_const(
            &ctx,
            prefix.clone() + &name.clone() + "0",
        )),
    };
    let new_name = prefix.clone() + &name;
    if variables.contains_key(&new_name.clone()) {
        fresh_variable(ctx, variables, counter, name, prefix);
    } else {
        variables.insert(new_name.clone() + "0", variable);
        counter.insert(new_name, 0);
    }
}

fn fresh_variable<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    name: String,
    prefix: String,
) -> Variable<'a> {
    let num = counter.get(&(prefix.clone() + &name.clone())).unwrap();
    let new_name = prefix.clone() + &name.clone() + &(num + 1).to_string();
    let var = match *(variables
        .get(&(prefix.clone() + &name.clone() + &num.to_string()))
        .unwrap())
    {
        Variable::Bool(_) => Variable::Bool(z3::ast::Bool::new_const(&ctx, new_name.clone())),
        Variable::Int(_) => Variable::Int(z3::ast::Int::new_const(&ctx, new_name.clone())),
    };
    variables.insert(new_name, var.clone());
    counter.insert(prefix + &name, num + 1);
    var
}

fn parse_params<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    params: Vec<ast::Var>,
    prefix: String,
) -> Vec<String> {
    let mut names = Vec::new();
    for param in params {
        let ast::Var { name, ty } = param;
        names.push(prefix.clone() + &name.text.clone());
        parse_type(&ctx, variables, counter, name.text, ty, prefix.clone());
    }
    names
}

// Parse specifications
fn parse_specs<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    specs: Vec<ast::Specification>,
    requires: bool,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<(Option<z3::ast::Bool<'a>>, Vec<Vec<z3::ast::Bool<'a>>>), Wrong> {
    let mut assumptions = assumptions;
    let mut conditions = Vec::new();
    let mut requires_has_already_reported: bool = false;
    for spec in specs {
        match spec {
            ast::Specification::Ensures(e) => {
                if requires {
                    continue;
                }
                let location = (e.span.start(), e.span.end());
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    e,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match match value {
                            Value::Bool(b) => Ok(z3::ast::Bool::from_bool(ctx, b)),
                            Value::Var(var) => match var {
                                Variable::Bool(b) => Ok(b),
                                _ => Err(Wrong {
                                    msg: "Ensures with a value that has wrong type".to_string(),
                                    span: location,
                                }),
                            },
                            _ => Err(Wrong {
                                msg: "Ensures with a value that has wrong type".to_string(),
                                span: location,
                            }),
                        } {
                            Ok(ensure) => {
                                conditions.push(ensure.clone());
                                match assert(ctx, &solver, &assumptions, ensure) {
                                    Ok(_) => {}
                                    Err(e) => {
                                        println!(
                                            "{:?}",
                                            generate_error(
                                                Wrong {
                                                    msg: e,
                                                    span: location,
                                                },
                                                code.clone(),
                                                path.clone()
                                            )
                                        );
                                    }
                                }
                            }
                            Err(e) => {
                                return Err(e);
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
            }
            ast::Specification::Requires(r) => {
                if !requires {
                    continue;
                }
                let location = (r.span.start(), r.span.end());
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    r,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match value {
                            Value::Bool(b) => {
                                conditions.push(z3::ast::Bool::from_bool(ctx, b));
                                if !b {
                                    requires_has_already_reported = true;
                                    println!(
                                    "{:?}",
                                    generate_error(
                                        Wrong {
                                            msg: "Warning: All assertions will not report error now".to_string(),
                                            span: location,
                                        },
                                        code.clone(),
                                        path.clone()
                                    )
                                );
                                }
                            }
                            Value::Var(var) => match var {
                                Variable::Bool(b) => {
                                    if !requires_has_already_reported {
                                        conditions.push(b);
                                        match assert(
                                            ctx,
                                            solver,
                                            &[conditions.clone()],
                                            z3::ast::Bool::from_bool(ctx, false),
                                        ) {
                                            Ok(_) => {
                                                requires_has_already_reported = true;
                                                println!(
                                                "{:?}",
                                                generate_error(
                                                    Wrong {
                                                        msg: "Warning: Contradict requires condition, all assertions will not report error now".to_string(),
                                                        span: location,
                                                    },
                                                    code.clone(),
                                                    path.clone()
                                                )
                                            );
                                            }
                                            Err(_) => {}
                                        }
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "Requires with a value that has wrong type"
                                            .to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "Requires with a value that has wrong type".to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
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
    if requires_has_already_reported {
        Ok((None, assumptions))
    } else {
        Ok((Some(condition), assumptions))
    }
}

fn parse_expr<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    expr: ast::Expr,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<(Value<'a>, Vec<Vec<z3::ast::Bool<'a>>>), String> {
    let kind = expr.kind;
    match parse_expr_kind(
        &ctx,
        variables,
        counter,
        kind,
        solver,
        assumptions,
        code,
        path,
        global_inputs.clone(),
        global_outputs.clone(),
        global_ensures.clone(),
        global_requires.clone(),
        global_functions.clone(),
        prefix,
    ) {
        Ok(value) => Ok(value),
        Err(e) => Err(e),
    }
}

fn parse_expr_kind<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    expr_kind: Box<ast::ExprKind>,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<(Value<'a>, Vec<Vec<z3::ast::Bool<'a>>>), String> {
    let mut assumptions = assumptions;
    match *expr_kind {
        ast::ExprKind::Boolean(b) => Ok((Value::Bool(b), assumptions)),
        ast::ExprKind::Integer(i) => Ok((Value::Int(i.parse().unwrap()), assumptions)),
        ast::ExprKind::Var(ident) => Ok((
            Value::Var(
                variables
                    .get(
                        &(prefix.clone()
                            + &ident.text.clone()
                            + &counter
                                .get(&(prefix.clone() + &ident.text))
                                .unwrap()
                                .to_string()),
                    )
                    .unwrap()
                    .clone(),
            ),
            assumptions,
        )),
        ast::ExprKind::Result => Ok((Value::Bool(true), assumptions)),
        ast::ExprKind::Call(ident, exprs) => {
            match pre_call(
                ctx,
                variables,
                counter,
                exprs,
                solver,
                assumptions.clone(),
                ident.clone(),
                code.clone(),
                path.clone(),
                global_inputs.clone(),
                global_outputs.clone(),
                global_ensures.clone(),
                global_requires.clone(),
                global_functions.clone(),
                prefix.clone(),
            ) {
                Ok(a) => {
                    assumptions = a;
                }
                Err(e) => {
                    println!("{:?}", generate_error(e, code.clone(), path.clone()));
                }
            }
            match global_functions.get(&ident.text).unwrap() {
                Some(expr) => parse_expr(
                    ctx,
                    variables,
                    counter,
                    expr.clone(),
                    solver,
                    assumptions,
                    code,
                    path,
                    global_inputs,
                    global_outputs,
                    global_ensures,
                    global_requires,
                    global_functions,
                    prefix + &ident.text + "-",
                ),
                None => Ok((
                    Value::Var(Variable::Bool(z3::ast::Bool::from_bool(ctx, true))),
                    assumptions,
                )),
            }
        }
        ast::ExprKind::Unary(uop, expr) => match parse_expr(
            &ctx,
            variables,
            counter,
            expr,
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone(),
        ) {
            Ok((value, a)) => {
                assumptions = a;
                match uop {
                    ast::UOp::Minus => match value {
                        Value::Int(i) => Ok((Value::Int(-i), assumptions)),
                        Value::Var(var) => match var {
                            Variable::Int(i) => {
                                Ok((Value::Var(Variable::Int(i.unary_minus())), assumptions))
                            }
                            _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                        },
                        _ => Err("UnaryOp - with a value that has wrong type".to_string()),
                    },
                    ast::UOp::Not => match value {
                        Value::Bool(i) => Ok((Value::Bool(!i), assumptions)),
                        Value::Var(var) => match var {
                            Variable::Bool(i) => {
                                Ok((Value::Var(Variable::Bool(i.not())), assumptions))
                            }
                            _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                        },
                        _ => Err("UnaryOp ! with a value that has wrong type".to_string()),
                    },
                }
            }
            Err(e) => Err(e),
        },
        ast::ExprKind::Binary(expr1, op, expr2) => {
            match parse_expr(
                &ctx,
                variables,
                counter,
                expr1,
                solver,
                assumptions,
                code.clone(),
                path.clone(),
                global_inputs.clone(),
                global_outputs.clone(),
                global_ensures.clone(),
                global_requires.clone(),
                global_functions.clone(),
                prefix.clone(),
            ) {
                Ok((value1, a)) => {
                    assumptions = a;
                    match parse_expr(
                        &ctx,
                        variables,
                        counter,
                        expr2,
                        solver,
                        assumptions,
                        code.clone(),
                        path.clone(),
                        global_inputs.clone(),
                        global_outputs.clone(),
                        global_ensures.clone(),
                        global_requires.clone(),
                        global_functions.clone(),
                        prefix.clone(),
                    ) {
                        Ok((value2, a)) => {
                            assumptions = a;
                            match op {
                                ast::Op::And => match value1 {
                                    Value::Bool(var1) => match value2 {
                                        Value::Bool(var2) => {
                                            Ok((Value::Bool(var1 && var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::and(
                                                        ctx,
                                                        &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                                    ))),
                                                    assumptions,
                                                )),
                                                _ => Err("&& with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("&& with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Bool(i) => {
                                            match value2 {
                                                Value::Bool(var2) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::and(
                                                        ctx,
                                                        &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Bool(i2) => Ok((
                                                        Value::Var(Variable::Bool(
                                                            z3::ast::Bool::and(ctx, &[&i, &i2]),
                                                        )),
                                                        assumptions,
                                                    )),
                                                    _ => Err("&& with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("&& with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("&& with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("&& with a value that has wrong type".to_string()),
                                },
                                ast::Op::Divide => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Int(var1 / var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Int(
                                                        z3::ast::Int::from_i64(ctx, var1).div(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("/ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("/ with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Int(
                                                        i.div(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Int(i.div(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("/ with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("/ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("/ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("/ with a value that has wrong type".to_string()),
                                },
                                ast::Op::Eq => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 == var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Int::from_i64(ctx, var1)._eq(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    Value::Bool(var1) => match value2 {
                                        Value::Bool(var2) => {
                                            Ok((Value::Bool(var1 == var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Bool::from_bool(ctx, var1)._eq(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("== with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => {
                                        match var {
                                            Variable::Int(i) => match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        i._eq(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Bool(i._eq(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("== with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            },
                                            Variable::Bool(i) => match value2 {
                                                Value::Bool(var2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(
                                                        &z3::ast::Bool::from_bool(ctx, var2),
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Bool(i2) => Ok((
                                                        Value::Var(Variable::Bool(i._eq(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("== with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("== with a value that has wrong type"
                                                    .to_string()),
                                            },
                                            // _ => Err("== with a value that has wrong type".to_string()),
                                        }
                                    } // _ => Err("== with a value that has wrong type".to_string()),
                                },
                                ast::Op::Geq => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 >= var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Int::from_i64(ctx, var1).ge(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err(">= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err(">= with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        i.ge(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Bool(i.ge(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err(">= with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err(">= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err(">= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err(">= with a value that has wrong type".to_string()),
                                },
                                ast::Op::Gt => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 > var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Int::from_i64(ctx, var1).gt(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("> with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("> with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        i.gt(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Bool(i.gt(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("> with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("> with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
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
                                            assumptions,
                                        )),
                                        Value::Var(var2) => match var2 {
                                            Variable::Bool(i) => Ok((
                                                Value::Var(Variable::Bool(
                                                    z3::ast::Bool::from_bool(ctx, var1).implies(&i),
                                                )),
                                                assumptions,
                                            )),
                                            _ => {
                                                Err("==> with a value that has wrong type"
                                                    .to_string())
                                            }
                                        },
                                        _ => {
                                            Err("==> with a value that has wrong type".to_string())
                                        }
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Bool(i) => match value2 {
                                            Value::Bool(var2) => Ok((
                                                Value::Var(Variable::Bool(i.implies(
                                                    &z3::ast::Bool::from_bool(ctx, var2),
                                                ))),
                                                assumptions,
                                            )),
                                            Value::Var(var2) => match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(i.implies(&i2))),
                                                    assumptions,
                                                )),
                                                _ => Err("==> with a value that has wrong type"
                                                    .to_string()),
                                            },
                                            _ => {
                                                Err("==> with a value that has wrong type"
                                                    .to_string())
                                            }
                                        },
                                        _ => {
                                            Err("==> with a value that has wrong type".to_string())
                                        }
                                    },
                                    _ => Err("==> with a value that has wrong type".to_string()),
                                },
                                ast::Op::Leq => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 <= var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Int::from_i64(ctx, var1).le(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("<= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("<= with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        i.le(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Bool(i.le(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("<= with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("<= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("<= with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("<= with a value that has wrong type".to_string()),
                                },
                                ast::Op::Lt => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 < var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Int::from_i64(ctx, var1).lt(&i),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("< with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("< with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        i.lt(&z3::ast::Int::from_i64(ctx, var2)),
                                                    )),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Bool(i.lt(&i2))),
                                                        assumptions,
                                                    )),
                                                    _ => Err("< with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("< with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("< with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("< with a value that has wrong type".to_string()),
                                },
                                ast::Op::Minus => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Int(var1 - var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::sub(
                                                        ctx,
                                                        &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                                    ))),
                                                    assumptions,
                                                )),
                                                _ => Err("- with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("- with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::sub(
                                                        ctx,
                                                        &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Int(
                                                            z3::ast::Int::sub(ctx, &[&i, &i2]),
                                                        )),
                                                        assumptions,
                                                    )),
                                                    _ => Err("- with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("- with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("- with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("- with a value that has wrong type".to_string()),
                                },
                                ast::Op::Neq => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Bool(var1 != var2), assumptions))
                                        }
                                        Value::Var(var2) => match var2 {
                                            Variable::Int(i) => Ok((
                                                Value::Var(Variable::Bool(
                                                    z3::ast::Int::from_i64(ctx, var1)._eq(&i).not(),
                                                )),
                                                assumptions,
                                            )),
                                            _ => {
                                                Err("!= with a value that has wrong type"
                                                    .to_string())
                                            }
                                        },
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    Value::Bool(var1) => match value2 {
                                        Value::Bool(var2) => {
                                            Ok((Value::Bool(var1 != var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i) => Ok((
                                                    Value::Var(Variable::Bool(
                                                        z3::ast::Bool::from_bool(ctx, var1)
                                                            ._eq(&i)
                                                            .not(),
                                                    )),
                                                    assumptions,
                                                )),
                                                _ => Err("!= with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => match value2 {
                                            Value::Int(var2) => Ok((
                                                Value::Var(Variable::Bool(
                                                    i._eq(&z3::ast::Int::from_i64(ctx, var2)).not(),
                                                )),
                                                assumptions,
                                            )),
                                            Value::Var(var2) => match var2 {
                                                Variable::Int(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2).not())),
                                                    assumptions,
                                                )),
                                                _ => Err("!= with a value that has wrong type"
                                                    .to_string()),
                                            },
                                            _ => {
                                                Err("!= with a value that has wrong type"
                                                    .to_string())
                                            }
                                        },
                                        Variable::Bool(i) => match value2 {
                                            Value::Bool(var2) => Ok((
                                                Value::Var(Variable::Bool(
                                                    i._eq(&z3::ast::Bool::from_bool(ctx, var2))
                                                        .not(),
                                                )),
                                                assumptions,
                                            )),
                                            Value::Var(var2) => match var2 {
                                                Variable::Bool(i2) => Ok((
                                                    Value::Var(Variable::Bool(i._eq(&i2).not())),
                                                    assumptions,
                                                )),
                                                _ => Err("!= with a value that has wrong type"
                                                    .to_string()),
                                            },
                                            _ => {
                                                Err("!= with a value that has wrong type"
                                                    .to_string())
                                            }
                                        },
                                        // _ => Err("!= with a value that has wrong type".to_string()),
                                    },
                                    // _ => Err("!= with a value that has wrong type".to_string()),
                                },
                                ast::Op::Or => match value1 {
                                    Value::Bool(var1) => match value2 {
                                        Value::Bool(var2) => {
                                            Ok((Value::Bool(var1 || var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Bool(i) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::or(
                                                        ctx,
                                                        &[&z3::ast::Bool::from_bool(ctx, var1), &i],
                                                    ))),
                                                    assumptions,
                                                )),
                                                _ => Err("|| with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("|| with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Bool(i) => {
                                            match value2 {
                                                Value::Bool(var2) => Ok((
                                                    Value::Var(Variable::Bool(z3::ast::Bool::or(
                                                        ctx,
                                                        &[&i, &z3::ast::Bool::from_bool(ctx, var2)],
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Bool(i2) => Ok((
                                                        Value::Var(Variable::Bool(
                                                            z3::ast::Bool::or(ctx, &[&i, &i2]),
                                                        )),
                                                        assumptions,
                                                    )),
                                                    _ => Err("|| with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("|| with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("|| with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("|| with a value that has wrong type".to_string()),
                                },
                                ast::Op::Plus => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Int(var1 + var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::add(
                                                        ctx,
                                                        &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                                    ))),
                                                    assumptions,
                                                )),
                                                _ => Err("+ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("+ with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::add(
                                                        ctx,
                                                        &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Int(
                                                            z3::ast::Int::add(ctx, &[&i, &i2]),
                                                        )),
                                                        assumptions,
                                                    )),
                                                    _ => Err("+ with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("+ with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("+ with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("+ with a value that has wrong type".to_string()),
                                },
                                ast::Op::Times => match value1 {
                                    Value::Int(var1) => match value2 {
                                        Value::Int(var2) => {
                                            Ok((Value::Int(var1 * var2), assumptions))
                                        }
                                        Value::Var(var2) => {
                                            match var2 {
                                                Variable::Int(i) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::mul(
                                                        ctx,
                                                        &[&z3::ast::Int::from_i64(ctx, var1), &i],
                                                    ))),
                                                    assumptions,
                                                )),
                                                _ => Err("* with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("* with a value that has wrong type".to_string()),
                                    },
                                    Value::Var(var) => match var {
                                        Variable::Int(i) => {
                                            match value2 {
                                                Value::Int(var2) => Ok((
                                                    Value::Var(Variable::Int(z3::ast::Int::mul(
                                                        ctx,
                                                        &[&i, &z3::ast::Int::from_i64(ctx, var2)],
                                                    ))),
                                                    assumptions,
                                                )),
                                                Value::Var(var2) => match var2 {
                                                    Variable::Int(i2) => Ok((
                                                        Value::Var(Variable::Int(
                                                            z3::ast::Int::mul(ctx, &[&i, &i2]),
                                                        )),
                                                        assumptions,
                                                    )),
                                                    _ => Err("* with a value that has wrong type"
                                                        .to_string()),
                                                },
                                                _ => Err("* with a value that has wrong type"
                                                    .to_string()),
                                            }
                                        }
                                        _ => Err("* with a value that has wrong type".to_string()),
                                    },
                                    _ => Err("* with a value that has wrong type".to_string()),
                                },
                            }
                        }
                        Err(e) => Err(e),
                    }
                }
                Err(e) => Err(e),
            }
        }
        ast::ExprKind::Quantification(quantifier, var, expr) => {
            let ast::Var { name, ty } = var;
            parse_type(
                &ctx,
                variables,
                counter,
                name.text.clone(),
                ty,
                prefix.clone(),
            );
            match parse_expr(
                &ctx,
                variables,
                counter,
                expr,
                solver,
                assumptions,
                code.clone(),
                path.clone(),
                global_inputs.clone(),
                global_outputs.clone(),
                global_ensures.clone(),
                global_requires.clone(),
                global_functions.clone(),
                prefix.clone(),
            ) {
                Ok((value, a)) => {
                    assumptions = a;
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
                                    &(prefix.clone()
                                        + &name.text.clone()
                                        + &counter
                                            .get(&(prefix.clone() + &name.text))
                                            .unwrap()
                                            .to_string()),
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
                                    assumptions,
                                )),
                                Variable::Int(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::forall_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    assumptions,
                                )),
                            }
                        }
                        ast::Quantifier::Exists => {
                            match variables
                                .get(
                                    &(prefix.clone()
                                        + &name.text.clone()
                                        + &counter
                                            .get(&(prefix.clone() + &name.text))
                                            .unwrap()
                                            .to_string()),
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
                                    assumptions,
                                )),
                                Variable::Int(bound) => Ok((
                                    Value::Var(Variable::Bool(z3::ast::exists_const(
                                        ctx,
                                        &[&bound],
                                        &[],
                                        &body,
                                    ))),
                                    assumptions,
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
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    body: ast::Body,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, Wrong> {
    let mut assumptions = assumptions;
    for stmt in body.statements {
        let location: (usize, usize);
        assumptions = match match stmt {
            ast::Statement::Var(var, expr) => {
                let ast::Var { name, ty } = var;
                parse_type(
                    &ctx,
                    variables,
                    counter,
                    name.text.clone(),
                    ty,
                    prefix.clone(),
                );
                match expr {
                    Some(expr) => parse_assignment(
                        ctx,
                        solver,
                        variables,
                        counter,
                        assumptions,
                        name,
                        expr,
                        code.clone(),
                        path.clone(),
                        global_inputs.clone(),
                        global_outputs.clone(),
                        global_ensures.clone(),
                        global_requires.clone(),
                        global_functions.clone(),
                        prefix.clone(),
                    ),
                    None => Ok(assumptions),
                }
            }
            ast::Statement::Assert(expr) => {
                location = (expr.span.start(), expr.span.end());
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    expr,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match value.clone() {
                            Value::Bool(b) => {
                                match assert(
                                    ctx,
                                    &solver,
                                    &assumptions,
                                    z3::ast::Bool::from_bool(ctx, b),
                                ) {
                                    Ok(_) => {}
                                    Err(e) => {
                                        println!(
                                            "{:?}",
                                            generate_error(
                                                Wrong {
                                                    msg: e,
                                                    span: location,
                                                },
                                                code.clone(),
                                                path.clone()
                                            )
                                        );
                                    }
                                };
                                Ok(assumptions)
                            }
                            Value::Var(var) => match var {
                                Variable::Bool(b) => {
                                    match assert(ctx, &solver, &assumptions, b) {
                                        Ok(_) => {}
                                        Err(e) => {
                                            println!(
                                                "{:?}",
                                                generate_error(
                                                    Wrong {
                                                        msg: e,
                                                        span: location,
                                                    },
                                                    code.clone(),
                                                    path.clone()
                                                )
                                            );
                                        }
                                    };
                                    Ok(assumptions)
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "Assert with a value that has wrong type".to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "Assert with a value that has wrong type".to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
            }
            ast::Statement::Assume(expr) => {
                location = (expr.span.start(), expr.span.end());
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    expr,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match value.clone() {
                            Value::Bool(b) => match add_assumption(
                                ctx,
                                solver,
                                assumptions.clone(),
                                Value::Var(Variable::Bool(z3::ast::Bool::from_bool(ctx, b))),
                                location.clone(),
                                code.clone(),
                                path.clone(),
                            ) {
                                Ok(a) => Ok(a),
                                Err(e) => {
                                    return Err(Wrong {
                                        msg: e,
                                        span: location,
                                    })
                                }
                            },
                            Value::Var(var) => match var {
                                Variable::Bool(_) => {
                                    match add_assumption(
                                        ctx,
                                        solver,
                                        assumptions.clone(),
                                        value,
                                        location.clone(),
                                        code.clone(),
                                        path.clone(),
                                    ) {
                                        Ok(a) => Ok(a),
                                        Err(e) => {
                                            return Err(Wrong {
                                                msg: e,
                                                span: location,
                                            })
                                        }
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "Assume with a value that has wrong type".to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "Assume with a value that has wrong type".to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
            }
            ast::Statement::Assignment(ident, expr) => parse_assignment(
                ctx,
                solver,
                variables,
                counter,
                assumptions,
                ident,
                expr,
                code.clone(),
                path.clone(),
                global_inputs.clone(),
                global_outputs.clone(),
                global_ensures.clone(),
                global_requires.clone(),
                global_functions.clone(),
                prefix.clone(),
            ),
            ast::Statement::MethodAssignment(idents, ident, exprs) => {
                let method_name = ident.text.clone();
                location = (ident.span.start(), ident.span.end());
                let method_output = parse_params(
                    ctx,
                    variables,
                    counter,
                    global_outputs.get(&method_name).unwrap().clone(),
                    prefix.clone() + &method_name.clone() + "-",
                );
                match pre_call(
                    ctx,
                    variables,
                    counter,
                    exprs,
                    solver,
                    assumptions,
                    ident,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok(a) => assumptions = a,
                    Err(e) => return Err(e),
                }
                for (index, ident) in idents.iter().enumerate() {
                    let var_name = method_output.get(index).unwrap().clone();
                    let out = variables
                        .get(&(var_name.clone() + &counter.get(&var_name).unwrap().to_string()))
                        .unwrap()
                        .clone();
                    match fresh_variable(
                        ctx,
                        variables,
                        counter,
                        ident.text.clone(),
                        prefix.clone(),
                    ) {
                        Variable::Bool(b) => match out {
                            Variable::Bool(b2) => {
                                match add_assumption(
                                    ctx,
                                    solver,
                                    assumptions,
                                    Value::Var(Variable::Bool(b._eq(&b2))),
                                    location,
                                    code.clone(),
                                    path.clone(),
                                ) {
                                    Ok(a) => assumptions = a,
                                    Err(e) => {
                                        return Err(Wrong {
                                            msg: e,
                                            span: location,
                                        })
                                    }
                                }
                            }
                            _ => {
                                return Err(Wrong {
                                    msg: "MethodAssignment with a value that has wrong type"
                                        .to_string(),
                                    span: location,
                                })
                            }
                        },
                        Variable::Int(i) => match out {
                            Variable::Int(i2) => {
                                match add_assumption(
                                    ctx,
                                    solver,
                                    assumptions,
                                    Value::Var(Variable::Bool(i._eq(&i2))),
                                    location,
                                    code.clone(),
                                    path.clone(),
                                ) {
                                    Ok(a) => assumptions = a,
                                    Err(e) => {
                                        return Err(Wrong {
                                            msg: e,
                                            span: location,
                                        })
                                    }
                                }
                            }
                            _ => {
                                return Err(Wrong {
                                    msg: "MethodAssignment with a value that has wrong type"
                                        .to_string(),
                                    span: location,
                                })
                            }
                        },
                    }
                }
                Ok(assumptions)
            }
            ast::Statement::If(expr, body, body_opt) => {
                location = (expr.span.start(), expr.span.end());
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    expr,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        let mut if_branch_counter = counter.clone();
                        let assumptions_if = match add_assumption(
                            ctx,
                            solver,
                            assumptions.clone(),
                            value.clone(),
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(if_ass) => {
                                match parse_body(
                                    &ctx,
                                    variables,
                                    &mut if_branch_counter,
                                    solver,
                                    if_ass,
                                    body,
                                    code.clone(),
                                    path.clone(),
                                    global_inputs.clone(),
                                    global_outputs.clone(),
                                    global_ensures.clone(),
                                    global_requires.clone(),
                                    global_functions.clone(),
                                    prefix.clone(),
                                ) {
                                    Ok(a) => a,
                                    Err(e) => return Err(e),
                                }
                            }
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
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
                                        _ => Err(Wrong {
                                            msg: "if condition with a value that has wrong type"
                                                .to_string(),
                                            span: location,
                                        }),
                                    },
                                    _ => Err(Wrong {
                                        msg: "if condition with a value that has wrong type"
                                            .to_string(),
                                        span: location,
                                    }),
                                } {
                                    Ok(else_ass) => {
                                        match add_assumption(
                                            ctx,
                                            solver,
                                            assumptions,
                                            else_ass,
                                            location.clone(),
                                            code.clone(),
                                            path.clone(),
                                        ) {
                                            Ok(else_assumptions) => {
                                                match parse_body(
                                                    &ctx,
                                                    variables,
                                                    &mut else_branch_counter,
                                                    solver,
                                                    else_assumptions,
                                                    body,
                                                    code.clone(),
                                                    path.clone(),
                                                    global_inputs.clone(),
                                                    global_outputs.clone(),
                                                    global_ensures.clone(),
                                                    global_requires.clone(),
                                                    global_functions.clone(),
                                                    prefix.clone(),
                                                ) {
                                                    Ok(final_ass) => post_choice_branch(
                                                        ctx,
                                                        solver,
                                                        variables,
                                                        counter,
                                                        &mut if_branch_counter,
                                                        &mut else_branch_counter,
                                                        assumptions_if.clone(),
                                                        final_ass,
                                                        location,
                                                        code.clone(),
                                                        path.clone(),
                                                    ),
                                                    Err(e) => Err(e),
                                                }
                                            }
                                            Err(e) => Err(Wrong {
                                                msg: e,
                                                span: location,
                                            }),
                                        }
                                    }
                                    Err(e) => Err(e),
                                }
                            }
                            None => Ok(assumptions_if.clone()),
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
            }
            ast::Statement::While {
                condition,
                invariants,
                body,
            } => {
                location = (condition.span.start(), condition.span.end());
                let mut parsed_invariants = vec![];
                let mut invariants_location = vec![];
                match parse_invariants(
                    ctx,
                    variables,
                    counter,
                    invariants.clone(),
                    &mut parsed_invariants,
                    &mut invariants_location,
                    solver,
                    assumptions.clone(),
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok(a) => {
                        assumptions = a;
                    }
                    Err(e) => return Err(e),
                }
                for (index, pi) in parsed_invariants.clone().iter().enumerate() {
                    match assert(ctx, solver, &assumptions, pi.clone()) {
                        Ok(_) => {}
                        Err(e) => {
                            println!(
                                "{:?}",
                                generate_error(
                                    Wrong {
                                        msg: e + " before we enter the while loop",
                                        span: invariants_location.get(index).unwrap().clone(),
                                    },
                                    code.clone(),
                                    path.clone()
                                )
                            );
                        }
                    }
                }
                let mut var_list: HashSet<String> = HashSet::new();
                peek_body(body.clone(), &mut var_list);
                // Check total correctness before we havoc
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    condition.clone(),
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((while_cond, a)) => {
                        assumptions = a;
                        match while_cond {
                            Value::Bool(b) => {
                                if b {
                                    println!(
                                    "{:?}",
                                    generate_error(Wrong {
                                        msg: "while condition is always true (total correctness)".to_string(),
                                        span: location,
                                    }, code.clone(), path.clone())
                                );
                                }
                            }
                            Value::Var(var) => match var {
                                Variable::Bool(b) => {
                                    match assert(ctx, solver, &[vec![]], b.clone()) {
                                        Ok(_) => {
                                            println!(
                                            "{:?}",
                                            generate_error(Wrong {
                                                msg: "while condition is always true (total correctness)".to_string(),
                                                span: location,
                                            }, code.clone(), path.clone())
                                        );
                                        }
                                        Err(_) => match assert(ctx, solver, &assumptions, b) {
                                            Ok(_) => {
                                                let mut expr_var_list: HashSet<String> =
                                                    HashSet::new();
                                                peek_expr(condition.clone(), &mut expr_var_list);
                                                let mut never_get_assigned = true;
                                                for var in expr_var_list {
                                                    if var_list.contains(&var) {
                                                        never_get_assigned = false;
                                                        break;
                                                    }
                                                }
                                                if never_get_assigned {
                                                    println!(
                                                        "{:?}",
                                                        generate_error(Wrong {
                                                            msg: "while condition is always true and value never got changed (total correctness)".to_string(),
                                                            span: location,
                                                        }, code.clone(), path.clone())
                                                    );
                                                }
                                            }
                                            Err(_) => {}
                                        },
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "while condition with a value that has wrong type"
                                            .to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "while condition with a value that has wrong type"
                                        .to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
                // havoc
                for var in var_list {
                    if counter.contains_key(&var) {
                        fresh_variable(ctx, variables, counter, var, prefix.clone());
                    }
                }
                match parse_invariants(
                    ctx,
                    variables,
                    counter,
                    invariants.clone(),
                    &mut parsed_invariants,
                    &mut invariants_location,
                    solver,
                    assumptions.clone(),
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok(a) => {
                        assumptions = a;
                    }
                    Err(e) => return Err(e),
                }
                for (index, pi) in parsed_invariants.clone().iter().enumerate() {
                    match add_assumption(
                        ctx,
                        solver,
                        assumptions,
                        Value::Var(Variable::Bool(pi.clone())),
                        location.clone(),
                        code.clone(),
                        path.clone(),
                    ) {
                        Ok(ass) => assumptions = ass,
                        Err(e) => {
                            return Err(Wrong {
                                msg: e,
                                span: invariants_location.get(index).unwrap().clone(),
                            })
                        }
                    }
                }
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    condition,
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((while_cond, a)) => {
                        assumptions = a;
                        // Check the while loop body
                        let mut not_while_assumptions = assumptions.clone();
                        let mut not_while_counter = counter.clone();
                        let mut while_assumptions = assumptions.clone();
                        let mut while_counter = counter.clone();
                        match add_assumption(
                            ctx,
                            solver,
                            while_assumptions,
                            while_cond.clone(),
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(ass) => while_assumptions = ass,
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
                        }
                        match parse_body(
                            &ctx,
                            variables,
                            &mut while_counter,
                            solver,
                            while_assumptions.clone(),
                            body,
                            code.clone(),
                            path.clone(),
                            global_inputs.clone(),
                            global_outputs.clone(),
                            global_ensures.clone(),
                            global_requires.clone(),
                            global_functions.clone(),
                            prefix.clone(),
                        ) {
                            Ok(ass) => while_assumptions = ass,
                            Err(e) => return Err(e),
                        }
                        match parse_invariants(
                            ctx,
                            variables,
                            &mut while_counter,
                            invariants,
                            &mut parsed_invariants,
                            &mut invariants_location,
                            solver,
                            assumptions,
                            code.clone(),
                            path.clone(),
                            global_inputs.clone(),
                            global_outputs.clone(),
                            global_ensures.clone(),
                            global_requires.clone(),
                            global_functions.clone(),
                            prefix.clone(),
                        ) {
                            Ok(_) => {}
                            // Ok(a) => {
                            //     assumptions = a;
                            // }
                            Err(e) => return Err(e),
                        }
                        for (index, pi) in parsed_invariants.clone().iter().enumerate() {
                            match assert(ctx, solver, &while_assumptions, pi.clone()) {
                                Ok(_) => {}
                                Err(e) => {
                                    println!(
                                        "{:?}",
                                        generate_error(
                                            Wrong {
                                                msg: e + " after we exit the while loop",
                                                span: invariants_location
                                                    .get(index)
                                                    .unwrap()
                                                    .clone(),
                                            },
                                            code.clone(),
                                            path.clone()
                                        )
                                    );
                                }
                            }
                        }
                        match add_assumption(
                            ctx,
                            solver,
                            while_assumptions,
                            Value::Bool(false),
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(ass) => while_assumptions = ass,
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
                        }
                        // After while loop
                        match add_assumption(
                            ctx,
                            solver,
                            not_while_assumptions,
                            match while_cond {
                                Value::Bool(b) => Value::Bool(!b),
                                Value::Var(var) => {
                                    match var {
                                        Variable::Bool(b) => Value::Var(Variable::Bool(b.not())),
                                        _ => return Err(Wrong {
                                            msg: "while condition with a value that has wrong type"
                                                .to_string(),
                                            span: location,
                                        }),
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "while condition with a value that has wrong type"
                                            .to_string(),
                                        span: location,
                                    })
                                }
                            },
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(ass) => not_while_assumptions = ass,
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
                        }
                        post_choice_branch(
                            ctx,
                            solver,
                            variables,
                            counter,
                            &mut while_counter,
                            &mut not_while_counter,
                            while_assumptions,
                            not_while_assumptions,
                            location,
                            code.clone(),
                            path.clone(),
                        )
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
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
    solver: &z3::Solver,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    ident: ast::Ident,
    expr: ast::Expr,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, Wrong> {
    let location: (usize, usize) = (expr.span.start(), expr.span.end());
    let mut assumptions = assumptions;
    match variables
        .clone()
        .get(
            &(prefix.clone()
                + &ident.text.clone()
                + &counter
                    .get(&(prefix.clone() + &ident.text.clone()))
                    .unwrap()
                    .to_string()),
        )
        .unwrap()
    {
        Variable::Bool(_) => match parse_expr(
            &ctx,
            variables,
            counter,
            expr,
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone(),
        ) {
            Ok((value, a)) => {
                assumptions = a;
                let assigned =
                    match fresh_variable(ctx, variables, counter, ident.text, prefix.clone()) {
                        Variable::Bool(b) => b,
                        _ => {
                            return Err(Wrong {
                                msg: "Assignment with a fresh value that has wrong type"
                                    .to_string(),
                                span: location,
                            })
                        }
                    };
                match value {
                    Value::Bool(b) => match add_assumption(
                        ctx,
                        solver,
                        assumptions.clone(),
                        Value::Var(Variable::Bool(
                            assigned._eq(&z3::ast::Bool::from_bool(ctx, b)),
                        )),
                        location.clone(),
                        code.clone(),
                        path.clone(),
                    ) {
                        Ok(a) => Ok(a),
                        Err(e) => {
                            return Err(Wrong {
                                msg: e,
                                span: location,
                            })
                        }
                    },
                    Value::Var(var) => match var {
                        Variable::Bool(b) => match add_assumption(
                            ctx,
                            solver,
                            assumptions.clone(),
                            Value::Var(Variable::Bool(assigned._eq(&b))),
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(a) => Ok(a),
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
                        },
                        _ => {
                            return Err(Wrong {
                                msg: "Assignment with a value that has wrong type".to_string(),
                                span: location,
                            })
                        }
                    },
                    _ => {
                        return Err(Wrong {
                            msg: "Assignment with a value that has wrong type".to_string(),
                            span: location,
                        })
                    }
                }
            }
            Err(e) => {
                return Err(Wrong {
                    msg: e,
                    span: location,
                })
            }
        },
        Variable::Int(_) => match parse_expr(
            &ctx,
            variables,
            counter,
            expr,
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone(),
        ) {
            Ok((value, a)) => {
                assumptions = a;
                let assigned =
                    match fresh_variable(ctx, variables, counter, ident.text, prefix.clone()) {
                        Variable::Int(i) => i,
                        _ => {
                            return Err(Wrong {
                                msg: "Assignment with a fresh value that has wrong type"
                                    .to_string(),
                                span: location,
                            })
                        }
                    };
                match value {
                    Value::Int(b) => match add_assumption(
                        ctx,
                        solver,
                        assumptions.clone(),
                        Value::Var(Variable::Bool(
                            assigned._eq(&z3::ast::Int::from_i64(ctx, b)),
                        )),
                        location.clone(),
                        code.clone(),
                        path.clone(),
                    ) {
                        Ok(a) => Ok(a),
                        Err(e) => {
                            return Err(Wrong {
                                msg: e,
                                span: location,
                            })
                        }
                    },
                    Value::Var(var) => match var {
                        Variable::Int(b) => match add_assumption(
                            ctx,
                            solver,
                            assumptions.clone(),
                            Value::Var(Variable::Bool(assigned._eq(&b))),
                            location.clone(),
                            code.clone(),
                            path.clone(),
                        ) {
                            Ok(a) => Ok(a),
                            Err(e) => {
                                return Err(Wrong {
                                    msg: e,
                                    span: location,
                                })
                            }
                        },
                        _ => {
                            return Err(Wrong {
                                msg: "Assignment with a value that has wrong type".to_string(),
                                span: location,
                            })
                        }
                    },
                    _ => {
                        return Err(Wrong {
                            msg: "Assignment with a value that has wrong type".to_string(),
                            span: location,
                        })
                    }
                }
            }
            Err(e) => {
                return Err(Wrong {
                    msg: e,
                    span: location,
                })
            }
        },
    }
}

fn post_choice_branch<'a>(
    ctx: &'a z3::Context,
    solver: &z3::Solver,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    if_branch_counter: &mut HashMap<String, i64>,
    else_branch_counter: &mut HashMap<String, i64>,
    assumptions_if: Vec<Vec<z3::ast::Bool<'a>>>,
    final_assumption: Vec<Vec<z3::ast::Bool<'a>>>,
    location: (usize, usize),
    code: String,
    path: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, Wrong> {
    let mut final_ass = final_assumption;
    let mut assumptions_if = assumptions_if;
    for key in counter.clone().keys() {
        let if_branch = if_branch_counter.get(key).unwrap();
        let else_branch = else_branch_counter.get(key).unwrap();
        let if_branch_var = variables
            .get(&(key.clone() + &if_branch.to_string()))
            .unwrap();
        let else_branch_var = variables
            .get(&(key.clone() + &else_branch.to_string()))
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
                        _ => {
                            return Err(Wrong {
                                msg: "Unmatched var in fresh var assignment".to_string(),
                                span: location,
                            })
                        }
                    },
                    Variable::Int(var1) => match else_branch_var {
                        Variable::Int(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                        _ => {
                            return Err(Wrong {
                                msg: "Unmatched var in fresh var assignment".to_string(),
                                span: location,
                            })
                        }
                    },
                },
                location.clone(),
                code.clone(),
                path.clone(),
            ) {
                Ok(a) => a,
                Err(e) => {
                    return Err(Wrong {
                        msg: e,
                        span: location,
                    })
                }
            }
        } else if else_branch > if_branch {
            num = else_branch.clone();
            assumptions_if = match add_assumption(
                ctx,
                solver,
                assumptions_if.clone(),
                match else_branch_var {
                    Variable::Bool(var1) => match if_branch_var {
                        Variable::Bool(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                        _ => {
                            return Err(Wrong {
                                msg: "Unmatched var in fresh var assignment".to_string(),
                                span: location,
                            })
                        }
                    },
                    Variable::Int(var1) => match if_branch_var {
                        Variable::Int(var2) => Value::Var(Variable::Bool(var1._eq(var2))),
                        _ => {
                            return Err(Wrong {
                                msg: "Unmatched var in fresh var assignment".to_string(),
                                span: location,
                            })
                        }
                    },
                },
                location.clone(),
                code.clone(),
                path.clone(),
            ) {
                Ok(a) => a,
                Err(e) => {
                    return Err(Wrong {
                        msg: e,
                        span: location,
                    })
                }
            };
        }
        counter.insert(key.clone(), num);
    }
    Ok(vec![assumptions_if.clone(), final_ass].concat())
}

fn peek_body<'a>(body: ast::Body, var_list: &mut HashSet<String>) {
    // For havoc
    for stmt in body.statements {
        match stmt {
            ast::Statement::Assignment(ident, _) => {
                var_list.insert(ident.text);
            }
            ast::Statement::MethodAssignment(idents, _, _) => {
                for i in idents {
                    var_list.insert(i.text);
                }
            }
            ast::Statement::If(_, body, body_opt) => {
                peek_body(body, var_list);
                match body_opt {
                    Some(b) => peek_body(b, var_list),
                    None => {}
                }
            }
            ast::Statement::While {
                condition: _,
                invariants: _,
                body,
            } => {
                peek_body(body, var_list);
            }
            _ => {}
        };
    }
}

fn peek_expr(expr: ast::Expr, var_list: &mut HashSet<String>) {
    match *expr.kind {
        ast::ExprKind::Var(ident) => {
            var_list.insert(ident.text);
        }
        ast::ExprKind::Call(_, exprs) => {
            for expr in exprs {
                peek_expr(expr, var_list)
            }
        }
        ast::ExprKind::Unary(_, expr1) => peek_expr(expr1, var_list),
        ast::ExprKind::Binary(expr1, _, expr2) => {
            peek_expr(expr1, var_list);
            peek_expr(expr2, var_list)
        }
        ast::ExprKind::Quantification(_, var, expr) => {
            let ast::Var { name, ty: _ } = var;
            var_list.insert(name.text);
            peek_expr(expr, var_list);
        }
        _ => {}
    }
}

fn parse_invariants<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    invariants: Vec<ast::Expr>,
    parsed_invariants: &mut Vec<z3::ast::Bool<'a>>,
    invariants_location: &mut Vec<(usize, usize)>,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, Wrong> {
    parsed_invariants.clear();
    invariants_location.clear();
    let mut assumptions = assumptions;
    for invariant in invariants {
        let invariant_location = (invariant.span.start(), invariant.span.end());
        invariants_location.push(invariant_location);
        match parse_expr(
            &ctx,
            variables,
            counter,
            invariant,
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone(),
        ) {
            Ok((i, a)) => {
                assumptions = a;
                match i {
                    Value::Bool(b) => parsed_invariants.push(z3::ast::Bool::from_bool(ctx, b)),
                    Value::Var(var) => match var {
                        Variable::Bool(b) => parsed_invariants.push(b),
                        _ => {
                            return Err(Wrong {
                                msg: "Invariant with a value that has wrong type".to_string(),
                                span: invariant_location,
                            })
                        }
                    },
                    _ => {
                        return Err(Wrong {
                            msg: "Invariant with a value that has wrong type".to_string(),
                            span: invariant_location,
                        })
                    }
                }
            }
            Err(e) => {
                return Err(Wrong {
                    msg: e,
                    span: invariant_location,
                })
            }
        };
    }
    Ok(assumptions)
}

fn pre_call<'a>(
    ctx: &'a z3::Context,
    variables: &mut HashMap<String, Variable<'a>>,
    counter: &mut HashMap<String, i64>,
    input_exprs: Vec<ast::Expr>,
    solver: &z3::Solver,
    assumptions: Vec<Vec<z3::ast::Bool<'a>>>,
    function: ast::Ident,
    code: String,
    path: String,
    global_inputs: HashMap<String, Vec<ast::Var>>,
    global_outputs: HashMap<String, Vec<ast::Var>>,
    global_ensures: HashMap<String, Vec<ast::Expr>>,
    global_requires: HashMap<String, Vec<ast::Expr>>,
    global_functions: HashMap<String, Option<ast::Expr>>,
    prefix: String,
) -> Result<Vec<Vec<z3::ast::Bool<'a>>>, Wrong> {
    let mut assumptions = assumptions;
    let mut location: (usize, usize);
    let call_name = function.text.clone();
    let call_input = parse_params(
        ctx,
        variables,
        counter,
        global_inputs.get(&call_name).unwrap().clone(),
        prefix.clone() + &call_name.clone() + "-",
    );

    for (index, expr) in input_exprs.iter().enumerate() {
        location = (expr.span.start(), expr.span.end());
        let full_name = call_input.get(index).unwrap().clone();
        match variables
            .clone()
            .get(&(full_name.clone() + &counter.get(&full_name).unwrap().to_string()))
            .unwrap()
        {
            Variable::Bool(var) => {
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    expr.clone(),
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match value {
                            Value::Bool(b) => {
                                match add_assumption(
                                    ctx,
                                    solver,
                                    assumptions,
                                    Value::Var(Variable::Bool(
                                        var._eq(&z3::ast::Bool::from_bool(ctx, b)),
                                    )),
                                    location,
                                    code.clone(),
                                    path.clone(),
                                ) {
                                    Ok(a) => assumptions = a,
                                    Err(e) => {
                                        return Err(Wrong {
                                            msg: e,
                                            span: location,
                                        })
                                    }
                                }
                            }
                            Value::Var(v) => match v {
                                Variable::Bool(b) => {
                                    match add_assumption(
                                        ctx,
                                        solver,
                                        assumptions,
                                        Value::Var(Variable::Bool(var._eq(&b))),
                                        location,
                                        code.clone(),
                                        path.clone(),
                                    ) {
                                        Ok(a) => assumptions = a,
                                        Err(e) => {
                                            return Err(Wrong {
                                                msg: e,
                                                span: location,
                                            })
                                        }
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "Call with a value that has wrong type".to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "Call with a value that has wrong type".to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                };
            }
            Variable::Int(var) => {
                match parse_expr(
                    &ctx,
                    variables,
                    counter,
                    expr.clone(),
                    solver,
                    assumptions,
                    code.clone(),
                    path.clone(),
                    global_inputs.clone(),
                    global_outputs.clone(),
                    global_ensures.clone(),
                    global_requires.clone(),
                    global_functions.clone(),
                    prefix.clone(),
                ) {
                    Ok((value, a)) => {
                        assumptions = a;
                        match value {
                            Value::Int(i) => {
                                match add_assumption(
                                    ctx,
                                    solver,
                                    assumptions,
                                    Value::Var(Variable::Bool(
                                        var._eq(&z3::ast::Int::from_i64(ctx, i)),
                                    )),
                                    location,
                                    code.clone(),
                                    path.clone(),
                                ) {
                                    Ok(a) => assumptions = a,
                                    Err(e) => {
                                        return Err(Wrong {
                                            msg: e,
                                            span: location,
                                        })
                                    }
                                }
                            }
                            Value::Var(v) => match v {
                                Variable::Int(i) => {
                                    match add_assumption(
                                        ctx,
                                        solver,
                                        assumptions,
                                        Value::Var(Variable::Bool(var._eq(&i))),
                                        location,
                                        code.clone(),
                                        path.clone(),
                                    ) {
                                        Ok(a) => assumptions = a,
                                        Err(e) => {
                                            return Err(Wrong {
                                                msg: e,
                                                span: location,
                                            })
                                        }
                                    }
                                }
                                _ => {
                                    return Err(Wrong {
                                        msg: "Call with a value that has wrong type".to_string(),
                                        span: location,
                                    })
                                }
                            },
                            _ => {
                                return Err(Wrong {
                                    msg: "Call with a value that has wrong type".to_string(),
                                    span: location,
                                })
                            }
                        }
                    }
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                };
            }
        }
    }
    location = (function.span.start(), function.span.end());
    for expr in global_requires.get(&call_name).unwrap() {
        let value = match parse_expr(
            ctx,
            variables,
            counter,
            expr.clone(),
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone() + &call_name.clone() + "-",
        ) {
            Ok((value, a)) => {
                assumptions = a;
                match value {
                    Value::Bool(b) => z3::ast::Bool::from_bool(ctx, b),
                    Value::Var(var) => match var {
                        Variable::Bool(b) => b,
                        _ => {
                            return Err(Wrong {
                                msg: "Call with a value that has wrong type".to_string(),
                                span: location,
                            })
                        }
                    },
                    _ => {
                        return Err(Wrong {
                            msg: "Call with a value that has wrong type".to_string(),
                            span: location,
                        })
                    }
                }
            }
            Err(e) => {
                return Err(Wrong {
                    msg: e,
                    span: location,
                })
            }
        };
        match assert(ctx, solver, &assumptions, value) {
            Ok(_) => {}
            Err(e) => {
                println!(
                    "{:?}",
                    generate_error(
                        Wrong {
                            msg: e,
                            span: location
                        },
                        code.clone(),
                        path.clone()
                    )
                );
            }
        }
    }
    for expr in global_ensures.get(&function.text).unwrap() {
        match parse_expr(
            ctx,
            variables,
            counter,
            expr.clone(),
            solver,
            assumptions,
            code.clone(),
            path.clone(),
            global_inputs.clone(),
            global_outputs.clone(),
            global_ensures.clone(),
            global_requires.clone(),
            global_functions.clone(),
            prefix.clone() + &function.text.clone() + "-",
        ) {
            Ok((value, a)) => {
                assumptions = a;
                match add_assumption(
                    ctx,
                    solver,
                    assumptions,
                    value,
                    location,
                    code.clone(),
                    path.clone(),
                ) {
                    Ok(a) => assumptions = a,
                    Err(e) => {
                        return Err(Wrong {
                            msg: e,
                            span: location,
                        })
                    }
                }
            }
            Err(e) => {
                return Err(Wrong {
                    msg: e,
                    span: location,
                })
            }
        }
    }
    Ok(assumptions)
}

fn check_method_total_correctness(body: ast::Body, name: String) -> (bool, (usize, usize)) {
    // For havoc
    for stmt in body.statements {
        match stmt {
            ast::Statement::MethodAssignment(_, ident, _) => {
                if ident.text == name {
                    return (false, (ident.span.start(), ident.span.end()));
                }
            }
            ast::Statement::If(_, body, body_opt) => {
                let (if_branch, location) = check_method_total_correctness(body, name.clone());
                let (else_branch, location) = match body_opt {
                    Some(b) => check_method_total_correctness(b, name.clone()),
                    None => (true, location),
                };
                // Both branches cannot have the method call at same time
                if !if_branch && !else_branch {
                    return (false, location);
                }
            }
            ast::Statement::While {
                condition: _,
                invariants: _,
                body,
            } => {
                let (while_branch, location) = check_method_total_correctness(body, name.clone());
                if !while_branch {
                    return (false, location);
                }
            }
            _ => {}
        };
    }
    (true, (0, 0))
}
