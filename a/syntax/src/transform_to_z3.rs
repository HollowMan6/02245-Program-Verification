use z3::{ast::Bool, ast::Int, SatResult, ast::Ast};
use crate::ast::{Document, DocumentItem, Statement, Expr, ExprKind, Op, Type};

/// 
#[derive(Debug)]
struct transform_to_z3 {
}

pub(crate) fn encode(doc: &Document) -> miette::Result<Document> {
    transform_to_z3::encode(doc)
}

impl transform_to_z3 {
    fn encode(doc: & Document) -> miette::Result<Document> {        
        let mut new_doc = doc.clone(); // Create a mutable copy of the document

        let assumes = Self::collect_assumes(&mut new_doc)?;

        Ok(new_doc)

    }

    fn collect_assumes(doc: &mut Document) -> miette::Result<Document> {
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                if let Some(body) = &mut method.body {
                    body.statements = body.statements.iter().map(|stmt| Self::encode_stmt(stmt)).collect();
    
                }
            }
        }
        // for item in &mut doc.items {
        //     if let Statement::Assert(expr) = item {
        //         let z3_expr = Self::to_z3_expr(expr.clone(), ctx);
        //         // ast::Type::Bool => Variable::Bool(z3::ast::Bool::new_const(&ctx, name.clone())),
        //         // ast::Type::Int => Variable::Int(z3::ast::Int::new_const(&ctx, name.clone())),   
        //     }
        // }
        Ok(doc.clone())
    }

    fn encode_stmt(stmt: &Statement) -> Statement {
        match stmt {
            Statement::Assert(expr) => {
                println!("{stmt:#?}"); 
                let cfg = z3::Config::new();
                let ctx = z3::Context::new(&cfg);
                let solver = z3::Solver::new(&ctx); 
                let cloned_expr = expr.clone();
                // let z3_expr = Self::to_z3_expr(&cloned_expr, &ctx);
                // // println!("Checking assumptions: {z3_expr:?}");
                // match solver.check_assumptions(&[*z3_expr]) {
                //     SatResult::Unsat => {
                //         println!(" + The assertions were unsatisfiable!");
                //         for unsat in solver.get_unsat_core() {
                //             dbg!(unsat);
                //         }
                //     }
                //     SatResult::Unknown => {
                //         println!(" + Maybe the assertions were satisfiable?");
                //         if let Some(model) = solver.get_model() {
                //             dbg!(model);
                //         } else {
                //             println!("Oh no, couldn't extract a model!")
                //         }
                //     }
                //     SatResult::Sat => {
                //         println!(" + The assertions were satisfiable!");
                //         let model = solver
                //             .get_model()
                //             .expect("a model exists since we got 'Sat'");
                //         dbg!(model);
                //     }
                // }
                Statement::Assert(expr.clone())          
            },
            Statement::Assume(expr) => {
                println!("{stmt:#?}"); 
                let cfg = z3::Config::new();
                let ctx = z3::Context::new(&cfg);
                let solver = z3::Solver::new(&ctx); 
                let cloned_expr = expr.clone();
                // let z3_expr = Self::to_z3_expr(&cloned_expr, &ctx);
                // // println!("Checking assumptions: {z3_expr:?}");
                // match solver.check_assumptions(&[*z3_expr]) {
                //     SatResult::Unsat => {
                //         println!(" + The assertions were unsatisfiable!");
                //         for unsat in solver.get_unsat_core() {
                //             dbg!(unsat);
                //         }
                //     }
                //     SatResult::Unknown => {
                //         println!(" + Maybe the assertions were satisfiable?");
                //         if let Some(model) = solver.get_model() {
                //             dbg!(model);
                //         } else {
                //             println!("Oh no, couldn't extract a model!")
                //         }
                //     }
                //     SatResult::Sat => {
                //         println!(" + The assertions were satisfiable!");
                //         let model = solver
                //             .get_model()
                //             .expect("a model exists since we got 'Sat'");
                //         dbg!(model);
                //     }
                // }
                Statement::Assume(expr.clone())          
            },
            st => {
                (st).clone()
            }
        }
    }

    // fn to_z3_expr<'a>(expr: &'a Expr, ctx: &'a z3::Context) -> Box<z3::ast::Bool<'a>> {
    //     match &*expr.kind {
    //         ExprKind::Binary(left, op, right) => {
    //             let left_z3 = Self::to_z3_expr_helper(left, ctx);
    //             let right_z3 = Self::to_z3_expr_helper(right, ctx);
    //             match op {
    //                 Op::Gt => Box::new(left_z3.gt(&*right_z3)),
    //                 // TODO: Handle other binary operators here
    //                 _ => panic!("Unsupported binary operator"),
    //             }
    //         }
    //         ExprKind::Var(_) => {
    //             // Assuming the existence of a variable is always true
    //             Box::new(Bool::from_bool(ctx, true))
    //         },
    //         ExprKind::Integer(_) => {
    //             // Assuming the existence of an integer is always true
    //             Box::new(Bool::from_bool(ctx, true))
    //         },
    //         // TODO: Handle other kinds of expressions here
    //         _ => panic!("Unsupported expression kind"),
    //     }
    // }
    
    // fn to_z3_expr_helper<'a>(expr: &'a Expr, ctx: &'a z3::Context) -> Box<dyn z3::ast::Ast<'a>> {
    //     match &*expr.kind {
    //         ExprKind::Binary(left, op, right) => {
    //             let left_z3 = Self::to_z3_expr_helper(left, ctx);
    //             let right_z3 = Self::to_z3_expr_helper(right, ctx);
    //             match op {
    //                 Op::Gt => Box::new(left_z3.gt(&*right_z3)),
    //                 // TODO: Handle other binary operators here
    //                 _ => panic!("Unsupported binary operator"),
    //             }
    //         }
    //         ExprKind::Var(name) => {
    //             match &expr.ty {
    //                 Type::Int => Box::new(z3::ast::Int::new_const(ctx, name.clone()).into()),
    //                 // TODO: Handle other types here
    //                 _ => panic!("Unsupported variable type"),
    //             }
    //         }
    //         ExprKind::Integer(value) => {
    //             // Assuming that value is an i64 or similar
    //             Box::new(z3::ast::Int::from_str(ctx, &value).into())
    //         },
    //         // TODO: Handle other kinds of expressions here
    //         _ => panic!("Unsupported expression kind"),
    //     }
    // }

    // fn to_z3_expr<'a>(expr: &'a Expr, ctx: &'a z3::Context) -> Box<z3::ast::Bool<'a>> {
    //     match &*expr.kind { // Dereference the Box but keep reference to the inner value
    //         ExprKind::Binary(_, op, _) => {
    //             let left_z3 = z3::ast::Int::new_const(ctx, "x");
    //             let right_z3 = z3::ast::Int::from_i64(ctx, 0);
                
    //             match op {
    //                 Op::Gt => Box::new(left_z3.gt(&right_z3)),
    //                 // TODO: Handle other binary operators here
    //                 _ => panic!("Unsupported binary operator"),
    //             }
    //         }
    //         ExprKind::Var(_) => {
    //             // Assuming the existence of a variable is always true
    //             Box::new(Bool::from_bool(ctx, true))
    //         },
    //         ExprKind::Integer(_) => {
    //             // Assuming the existence of an integer is always true
    //             Box::new(Bool::from_bool(ctx, true))
    //         },
    //         // TODO: Handle other kinds of expressions here
    //         _ => panic!("Unsupported expression kind"),
    //     }
    // }

    // fn to_z3_expr<'a>(expr: &'a Expr, ctx: &'a z3::Context) -> Box<dyn z3::ast::Ast<'a>> {
    //     match *expr.kind.clone() {
    //         ExprKind::Binary(left, op, right) => {
    //             let left_z3 = Self::to_z3_expr(&left, ctx);
    //             let right_z3 = Self::to_z3_expr(&right, ctx);
    //             match op {
    //                 Op::Gt => Box::new(left_z3.gt(&*right_z3)),
    //                 // TODO: Handle other binary operators here
    //                 _ => panic!("Unsupported binary operator"),
    //             }
    //         }
    //         ExprKind::Var(name) => {
    //             match &expr.ty {
    //                 Type::Int => Box::new(z3::ast::Int::new_const(ctx, name.clone()).into()),
    //                 // TODO: Handle other types here
    //                 _ => panic!("Unsupported variable type"),
    //             }
    //         }
    //         ExprKind::Integer(value) => {
    //             Box::new(z3::ast::Int::from_str(ctx, &value).into())
    //         }
    //         // TODO: Handle other kinds of expressions here
    //         _ => panic!("Unsupported expression kind"),
    //     }
    // }
}