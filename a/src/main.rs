use miette::Result;
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
                        inputs: _,
                        outputs: _,
                        specifications,
                        body,
                    } = method;
                    match parse_specs(&ctx, specifications) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };

                    let b = match body {
                        Some(b) => b,
                        None => continue,
                    };
                    match parse_body(&ctx, b) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                }
                ast::DocumentItem::Function(function) => {
                    // Access fields of function
                    let ast::Function {
                        name: _,
                        inputs: _,
                        ret_ty: _,
                        specifications,
                        body,
                    } = function;
                    match parse_specs(&ctx, specifications) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                    match body {
                        Some(body) => {
                            match parse_expr(&ctx, body) {
                                Ok(()) => {}
                                Err(_) => continue,
                            };
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

fn parse_type(ctx: &z3::Context, ty: ast::Type) -> Result<()> {
    match ty {
        ast::Type::Bool => {
            println!("Type: Bool");
        }
        ast::Type::Int => {
            println!("Type: Int");
        }
    }
    Ok(())
}

// Parse specifications
fn parse_specs(ctx: &z3::Context, specs: Vec<ast::Specification>) -> Result<()> {
    for spec in specs {
        match spec {
            ast::Specification::Ensures(ensures) => {
                match parse_expr(&ctx, ensures) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
            ast::Specification::Requires(requires) => {
                match parse_expr(&ctx, requires) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
        }
    }
    Ok(())
}

fn parse_expr(ctx: &z3::Context, expr: ast::Expr) -> Result<()> {
    let kind = expr.kind;
    let ty = expr.ty;
    match parse_expr_kind(&ctx, kind) {
        Ok(()) => {}
        Err(_) => {}
    };
    match parse_type(&ctx, ty) {
        Ok(()) => {}
        Err(_) => {}
    };
    Ok(())
}

fn parse_expr_kind(ctx: &z3::Context, expr_kind: Box<ast::ExprKind>) -> Result<()> {
    match *expr_kind {
        ast::ExprKind::Boolean(b) => {
            println!("Boolean: {}", b);
        }
        ast::ExprKind::Integer(i) => {
            println!("Integer: {}", i);
        }
        ast::ExprKind::Result => {
            println!("Result");
        }
        ast::ExprKind::Var(ident) => {
            println!("Var: {}", ident.text);
        }
        ast::ExprKind::Call(ident, exprs) => {
            println!("Call: {}", ident.text);
            for expr in exprs {
                match parse_expr(&ctx, expr) {
                    Ok(()) => {}
                    Err(_) => {}
                };
            }
        }
        ast::ExprKind::Unary(uop, expr) => {
            match uop {
                ast::UOp::Minus => {
                    println!("UnaryOp: -");
                }
                ast::UOp::Not => {
                    println!("UnaryOp: !");
                }
            }
            match parse_expr(&ctx, expr) {
                Ok(()) => {}
                Err(_) => {}
            };
        }
        ast::ExprKind::Binary(expr1, op, expr2) => {
            match parse_expr(&ctx, expr1) {
                Ok(()) => {}
                Err(_) => {}
            };
            match op {
                ast::Op::And => {
                    println!("BinaryOp: &&");
                }
                ast::Op::Divide => {
                    println!("BinaryOp: /");
                }
                ast::Op::Eq => {
                    println!("BinaryOp: ==");
                }
                ast::Op::Geq => {
                    println!("BinaryOp: >=");
                }
                ast::Op::Gt => {
                    println!("BinaryOp: >");
                }
                ast::Op::Implies => {
                    println!("BinaryOp: ==>");
                }
                ast::Op::Leq => {
                    println!("BinaryOp: <=");
                }
                ast::Op::Lt => {
                    println!("BinaryOp: <");
                }
                ast::Op::Minus => {
                    println!("BinaryOp: -");
                }
                ast::Op::Neq => {
                    println!("BinaryOp: !=");
                }
                ast::Op::Or => {
                    println!("BinaryOp: ||");
                }
                ast::Op::Plus => {
                    println!("BinaryOp: +");
                }
                ast::Op::Times => {
                    println!("BinaryOp: *");
                }
            }
            match parse_expr(&ctx, expr2) {
                Ok(()) => {}
                Err(_) => {}
            };
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
            match parse_type(&ctx, ty) {
                Ok(()) => {}
                Err(_) => {}
            };
            match parse_expr(&ctx, expr) {
                Ok(()) => {}
                Err(_) => {}
            };
        }
    }
    Ok(())
}

// Parse body
fn parse_body(ctx: &z3::Context, body: ast::Body) -> Result<()> {
    for stmt in body.statements {
        match stmt {
            ast::Statement::Var(var, expr) => {
                let ast::Var { name, ty } = var;
                println!("Var: {}", name.text);
                match parse_type(&ctx, ty) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
                match expr {
                    Some(expr) => {
                        match parse_expr(&ctx, expr) {
                            Ok(()) => {}
                            Err(_) => continue,
                        };
                    }
                    None => continue,
                }
            }
            ast::Statement::Assert(expr) => {
                match parse_expr(&ctx, expr) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::Assume(expr) => {
                match parse_expr(&ctx, expr) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::Assignment(ident, expr) => {
                println!("Assignment: {}", ident.text);
                match parse_expr(&ctx, expr) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
            ast::Statement::MethodAssignment(idents, ident, exprs) => {
                println!("MethodAssignment: {}", ident.text);
                for ident in idents {
                    println!("Var: {}", ident.text);
                }
                for expr in exprs {
                    match parse_expr(&ctx, expr) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                }
            }
            ast::Statement::If(expr, body, body_opt) => {
                match parse_expr(&ctx, expr) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
                match parse_body(&ctx, body) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
                match body_opt {
                    Some(body) => {
                        match parse_body(&ctx, body) {
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
                match parse_expr(&ctx, condition) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
                for invariant in invariants {
                    match parse_expr(&ctx, invariant) {
                        Ok(()) => {}
                        Err(_) => continue,
                    };
                }
                match parse_body(&ctx, body) {
                    Ok(()) => {}
                    Err(_) => continue,
                };
            }
        }
    }
    Ok(())
}
