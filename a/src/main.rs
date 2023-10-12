use miette::Result;
use syntax::ast::{Op, UOp};
pub use syntax::{self, ast};
use std::collections::HashMap;

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
                            parse_expr(&ctx, &mut variables, body)?;
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

enum Variable<'a> {
    Bool(z3::ast::Bool<'a>),
    Int(z3::ast::Int<'a>),
}

enum Value {
    Bool(bool),
    Int(i64),
    Var(String),
    Op(Op),
    UOp(UOp)
}

fn parse_type<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, name: String, ty: ast::Type) {
    let variable = match ty {
        ast::Type::Bool => Variable::Bool(z3::ast::Bool::new_const(&ctx, name.clone())),
        ast::Type::Int => Variable::Int(z3::ast::Int::new_const(&ctx, name.clone())),
    };
    variables.insert(name, variable);
}

fn parse_params<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, params: Vec<ast::Var>) -> Result<()> {
    for param in params {
        let ast::Var { name, ty } = param;
        parse_type(&ctx, variables, name.text, ty);
    }
    Ok(())
}

// Parse specifications
fn parse_specs<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, specs: Vec<ast::Specification>) -> Result<()> {
    for spec in specs {
        match spec {
            ast::Specification::Ensures(ensures) => {
                match parse_expr(&ctx, variables, ensures) {
                    Ok(_value) => {
                    }
                    Err(_) => continue,
                };
            }
            ast::Specification::Requires(requires) => {
                match parse_expr(&ctx, variables, requires) {
                    Ok(_value) => {}
                    Err(_) => continue,
                };
            }
        }
    }
    Ok(())
}

fn parse_expr<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, expr: ast::Expr) -> Result<Value> {
    let kind = expr.kind;
    let ty = expr.ty;
    match parse_expr_kind(&ctx, variables, kind) {
        Ok(_value) => {}
        Err(_) => {}
    };
    match ty {
        ast::Type::Bool => Ok(Value::Bool(true)),
        ast::Type::Int => Ok(Value::Int(0)),
    }
}

fn parse_expr_kind<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, expr_kind: Box<ast::ExprKind>) -> Result<Value> {
    match *expr_kind {
        ast::ExprKind::Boolean(b) => {
            return Ok(Value::Bool(b));
        }
        ast::ExprKind::Integer(i) => {
            return Ok(Value::Int(i.parse().unwrap()));
        }
        ast::ExprKind::Result => {
            // ask about this.
            println!("Result");
        }
        ast::ExprKind::Var(ident) => {
            return Ok(Value::Var(ident.text));
        }
        ast::ExprKind::Call(ident, exprs) => {
            println!("Call: {}", ident.text);
            for expr in exprs {
                // TODO: handle multiple exprs
                return Ok(parse_expr(&ctx, variables, expr)?);
            }
        }
        ast::ExprKind::Unary(uop, expr) => {
            match parse_expr(&ctx, variables, expr) {
                Ok(_value) => {}
                Err(_) => {}
            };
            match uop {
                ast::UOp::Minus => {
                    println!("UnaryOp: -");
                    return Ok(Value::UOp(UOp::Minus));
                }
                ast::UOp::Not => {
                    println!("UnaryOp: !");
                    return Ok(Value::UOp(UOp::Not));
                }
            } 
        }
        ast::ExprKind::Binary(expr1, op, expr2) => {
            // Give some example for this you have in mind?
            match parse_expr(&ctx, variables, expr1) {
                Ok(_value) => {}
                Err(_) => {}
            };
            match parse_expr(&ctx, variables, expr2) {
                Ok(_value) => {}
                Err(_) => {}
            };
            match op {
                ast::Op::And => {
                    println!("BinaryOp: &&");
                     return Ok(Value::Op(Op::And));
                }
                ast::Op::Divide => {
                    println!("BinaryOp: /");
                    return Ok(Value::Op(Op::Divide));

                }
                ast::Op::Eq => {
                    println!("BinaryOp: ==");
                    return Ok(Value::Op(Op::Eq));

                }
                ast::Op::Geq => {
                    println!("BinaryOp: >=");
                    return Ok(Value::Op(Op::Geq));

                }
                ast::Op::Gt => {
                    println!("BinaryOp: >");
                    return Ok(Value::Op(Op::Gt));
                }
                ast::Op::Implies => {
                    println!("BinaryOp: ==>");
                    return Ok(Value::Op(Op::Implies));

                }
                ast::Op::Leq => {
                    println!("BinaryOp: <=");
                    return Ok(Value::Op(Op::Leq));
                }
                ast::Op::Lt => {
                    println!("BinaryOp: <");
                    return Ok(Value::Op(Op::Lt));
                }
                ast::Op::Minus => {
                    println!("BinaryOp: -");
                    return Ok(Value::Op(Op::Minus));
                }
                ast::Op::Neq => {
                    println!("BinaryOp: !=");
                    return Ok(Value::Op(Op::Neq));
                }
                ast::Op::Or => {
                    println!("BinaryOp: ||");
                    return Ok(Value::Op(Op::Or));
                }
                ast::Op::Plus => {
                    println!("BinaryOp: +");
                    return Ok(Value::Op(Op::Plus));
                }
                ast::Op::Times => {
                    println!("BinaryOp: *");
                    return Ok(Value::Op(Op::Times));
                }
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
                Ok(_value) => {}
                Err(_) => {}
            };
        }
    }
    Ok(Value::Bool(true))
}

// Parse body
fn parse_body<'a>(ctx: &'a z3::Context, variables: &mut HashMap<String, Variable<'a>>, body: ast::Body) -> Result<()> {
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
