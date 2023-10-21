use z3::{ast::Bool, ast::Int, SatResult, ast::Ast, Context};
use crate::ast::{Document, DocumentItem, Statement, Expr, ExprKind, Op, UOp, Type, EK};
use std::fs::File;
use std::io::Write;
use std::fs::OpenOptions;
use std::process::Command;
use std::collections::HashSet;
use std::collections::HashMap;


/// 
#[derive(Debug)]
struct transform_to_z3 {
}

pub(crate) fn encode(doc: &Document) -> miette::Result<Document> {
    transform_to_z3::encode(doc)
}

#[derive(Clone, Debug)]
enum Z3Ast<'a> {
    Bool(Bool<'a>),
    Int(Int<'a>),
}

impl transform_to_z3 {
    fn encode(doc: & Document) -> miette::Result<Document> {        
        let mut new_doc = doc.clone(); // Create a mutable copy of the document

        let assumes_and_asserts_map = Self::collect_assumes_and_asserts(&mut new_doc)?;

        let mut all_methods_verified = true;
        for (method_name, assumes_and_asserts) in &assumes_and_asserts_map {

            // println!("{assumes_and_asserts:#?}");

            let cfg = z3::Config::new();
            let ctx = z3::Context::new(&cfg);
            let solver = z3::Solver::new(&ctx);
            
            // let x = Int::new_const(&ctx, "x");
            // let r = Int::new_const(&ctx, "r");
            let variables = Self::extract_variables(&assumes_and_asserts);
            let mut z3_vars = HashMap::new();
            for var_name in variables.iter() {
                z3_vars.insert(var_name.clone(), Int::new_const(&ctx, &**var_name));
            }
            // println!("{z3_vars:#?}");

            let final_conditions = Self::translate_statements_to_z3(&assumes_and_asserts, &ctx);

            if final_conditions.is_empty() {
                // If there are no Assert statements, return the combined Assume conditions.
                let final_conditions = Self::translate_statements_with_no_assert_to_z3(&assumes_and_asserts, &ctx);

                let condition = &final_conditions[0];
                match condition {
                    Z3Ast::Bool(cond) => {
                        println!("{cond:#?}");
                        solver.push(); // Save the current state of the solver
                        solver.assert(cond);
                        match solver.check() {
                            SatResult::Sat => println!("Verified"), // The combined Assume conditions are satisfiable
                            _ => println!("Unverified"), // Any other result means they are not verified
                        }
                        solver.pop(1); // Revert the solver to the saved state
                    }
                    _ => panic!("Expected Bool type for final condition"),
                }
            } else {
                let mut all_unsatisfiable = true; // assume all conditions are unsatisfiable to begin with
                
                for condition in &final_conditions {
                    match condition {
                        Z3Ast::Bool(cond) => {
                            let not_condition = !cond.clone(); // Negate the condition
                            println!("{not_condition:#?}");
                            solver.push(); // Save the current state of the solver
                            solver.assert(&not_condition);
                            match solver.check() {
                                SatResult::Unsat => {} // This is expected, continue to the next condition
                                SatResult::Sat => {
                                    all_unsatisfiable = false;
                                    break; // break out of the loop as we found a satisfiable condition
                                }
                                _ => {
                                    println!("Unknown result from solver");
                                    all_unsatisfiable = false;
                                    break;
                                }
                            }
                            solver.pop(1); // Revert the solver to the saved state
                        }
                        _ => panic!("Expected Bool type for final condition"),
                    }
                }
                
                if !all_unsatisfiable {
                    all_methods_verified = false;
                } 
            }
        }

        if all_methods_verified {
            println!("Verified");
        } else {
            println!("Unverified");
        }

        // println!("{assumes_and_asserts:#?}");

        // let output = Command::new("python3")  // or just "python" depending on your setup
        //     .arg("../python-z3/verf_a.py")
        //     .output()
        //     .expect("Failed to execute Python script.");

        // if output.status.success() {
        //     let output_str = String::from_utf8_lossy(&output.stdout);
        //     println!("Script output:\n{}", output_str);
        // } else {
        //     let error_str = String::from_utf8_lossy(&output.stderr);
        //     eprintln!("Script error:\n{}", error_str);
        // }

        Ok(new_doc)

    }

    fn extract_variables(statements: &Vec<Statement>) -> HashSet<String> {
        let mut variables = HashSet::new();
        for statement in statements {
            match statement {
                Statement::Assert(expr) | Statement::Assume(expr) => {
                    Self::collect_variables_from_expr(expr, &mut variables);
                }
                _ => {}
            }
        }
        variables
    }
    
    fn collect_variables_from_expr(expr: &Expr, vars: &mut HashSet<String>) {
        match &*expr.kind {
            EK::Var(ident) => {
                vars.insert(ident.text.clone());
            }
            EK::Unary(_, subexpr) => {
                Self::collect_variables_from_expr(subexpr, vars);
            }
            EK::Binary(lhs, _, rhs) => {
                Self::collect_variables_from_expr(lhs, vars);
                Self::collect_variables_from_expr(rhs, vars);
            }
            _ => {}
        }
    }

    fn collect_assumes_and_asserts(doc: &mut Document) -> miette::Result<HashMap<String, Vec<Statement>>> {
        let mut method_statements: HashMap<String, Vec<Statement>> = HashMap::new();
        
        for item in &mut doc.items {
            if let DocumentItem::Method(method) = item {
                let mut list: Vec<Statement> = Vec::new();
    
                if let Some(body) = &mut method.body {
                    body.statements = body.statements.iter()
                        .filter_map(|stmt| {
                            match Self::encode_stmt(stmt, &mut list) {
                                Ok(s) => Some(s),
                                Err(e) => {
                                    // Handle or log the error
                                    println!("Error processing statement: {}", e);
                                    None
                                }
                            }
                        })
                        .collect();
                }
    
                // Assuming method has a name field or something similar
                method_statements.insert(method.name.text.clone(), list);
            }
        }
        
        Ok(method_statements)
    }

    fn clear_file_content(filename: &str) -> std::io::Result<()> {
        let _file = OpenOptions::new()
            .write(true)        // We want to write to the file
            .truncate(true)     // This will clear the file's contents
            .open(filename)?;
        Ok(())
    }

    fn encode_stmt(stmt: &Statement, list: &mut Vec<Statement>) -> Result<Statement, std::io::Error> {
        match stmt {
            Statement::Assert(expr) => {
                // println!("{stmt:#?}"); 
                // let mut file = OpenOptions::new()
                //     .append(true)  // This enables appending mode
                //     .create(true)  // This will create the file if it doesn't exist
                //     .open("output.txt")?;
                // write!(file, "{:#?}\n", stmt)?;
                list.push(stmt.clone());
                Ok(Statement::Assert(expr.clone()))          
            },
            Statement::Assume(expr) => {
                // println!("{stmt:#?}"); 
                // let mut file = OpenOptions::new()
                //     .append(true)  // This enables appending mode
                //     .create(true)  // This will create the file if it doesn't exist
                //     .open("output.txt")?;
                // write!(file, "{:#?}\n", stmt)?;
                list.push(stmt.clone());
                Ok(Statement::Assume(expr.clone()))         
            },
            st => {
                Ok(st.clone())
            }
        }
    }

    fn translate_expr_to_z3<'a>(expr: &Expr, ctx: &'a Context) -> Z3Ast<'a> {
        match &*expr.kind {
            EK::Boolean(b) => Z3Ast::Bool(Bool::from_bool(ctx, *b)),
            // EK::Integer(i) => Z3Ast::Int(Int::from_str(ctx, &i.to_string())),
            EK::Integer(i) => Z3Ast::Int(Int::from_str(ctx, &i.to_string()).unwrap()),
            EK::Var(ident) => Z3Ast::Int(Int::new_const(ctx, &*ident.text)),
            EK::Unary(op, subexpr) => {
                let translated_subexpr = Self::translate_expr_to_z3(subexpr, ctx);
                match op {
                    UOp::Minus => Z3Ast::Int(-match translated_subexpr {
                        Z3Ast::Int(val) => val,
                        _ => panic!("Expected Int type"),
                    }),
                    UOp::Not => Z3Ast::Bool(!match translated_subexpr {
                        Z3Ast::Bool(val) => val,
                        _ => panic!("Expected Bool type"),
                    }),
                }
            }
            EK::Binary(lhs, op, rhs) => {
                let translated_lhs = Self::translate_expr_to_z3(lhs, ctx);
                let translated_rhs = Self::translate_expr_to_z3(rhs, ctx);
                match op {
                    Op::And => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Bool(lhs_val), Z3Ast::Bool(rhs_val)) => lhs_val & rhs_val,
                        _ => panic!("Expected Bool types for And operation"),
                    }),
                    Op::Or => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Bool(lhs_val), Z3Ast::Bool(rhs_val)) => lhs_val | rhs_val,
                        _ => panic!("Expected Bool types for Or operation"),
                    }),
                    Op::Eq => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Bool(lhs_val), Z3Ast::Bool(rhs_val)) => lhs_val._eq(&rhs_val),
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val._eq(&rhs_val),
                        _ => panic!("Incompatible types for Eq operation"),
                    }),
                    Op::Gt => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val.gt(&rhs_val),
                        _ => panic!("Expected Int types for Gt operation"),
                    }),
                    Op::Lt => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val.lt(&rhs_val),
                        _ => panic!("Expected Int types for Lt operation"),
                    }),
                    Op::Geq => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val.ge(&rhs_val),
                        _ => panic!("Expected Int types for Geq operation"),
                    }),
                    Op::Leq => Z3Ast::Bool(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val.le(&rhs_val),
                        _ => panic!("Expected Int types for Leq operation"),
                    }),
                    Op::Plus => Z3Ast::Int(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val + rhs_val,
                        _ => panic!("Expected Int types for Plus operation"),
                    }),
                    Op::Minus => Z3Ast::Int(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val - rhs_val,
                        _ => panic!("Expected Int types for Minus operation"),
                    }),
                    Op::Times => Z3Ast::Int(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val * rhs_val,
                        _ => panic!("Expected Int types for Times operation"),
                    }),
                    Op::Divide => Z3Ast::Int(match (translated_lhs, translated_rhs) {
                        (Z3Ast::Int(lhs_val), Z3Ast::Int(rhs_val)) => lhs_val / rhs_val,
                        _ => panic!("Expected Int types for Divide operation"),
                    }),
                    _ => panic!("Unsupported binary operation"),
                }
            }
            _ => panic!("Unsupported expression kind"),
        }
    }

    fn translate_statements_to_z3<'a>(statements: &Vec<Statement>, ctx: &'a Context) -> Vec<Z3Ast<'a>> {
        let mut assume_conditions: Vec<Bool<'a>> = Vec::new();
        let mut result_conditions: Vec<Z3Ast<'a>> = Vec::new();
    
        for statement in statements {
            match statement {
                Statement::Assume(expr) => {
                    let z3_expr = Self::translate_expr_to_z3(expr, ctx);
                    let assume_val = match &z3_expr {
                        Z3Ast::Bool(val) => val.clone(),
                        // handle other variants if necessary...
                        _ => panic!("Expected a boolean expression"),
                    };
                    assume_conditions.push(assume_val);
                }
                Statement::Assert(expr) => {
                    let z3_expr = Self::translate_expr_to_z3(expr, ctx);
                    let assert_val = match &z3_expr {
                        Z3Ast::Bool(val) => val,
                        // handle other variants if necessary...
                        _ => panic!("Expected a boolean expression"),
                    };
    
                    let combined_assume = assume_conditions.iter().fold(Bool::from_bool(ctx, true), |acc, x| Bool::and(ctx, &[&acc, x]));
                    result_conditions.push(Z3Ast::Bool(combined_assume.implies(assert_val)));
                }
                _ => {} 
            }
        }

        // // If there are no Assert statements, return the combined Assume conditions.
        // if result_conditions.is_empty() && !assume_conditions.is_empty() {
        //     let combined_assume = assume_conditions.iter().fold(Bool::from_bool(ctx, true), |acc, x| Bool::and(ctx, &[&acc, x]));
        //     result_conditions.push(Z3Ast::Bool(combined_assume));
        // }

        result_conditions
    }

    fn translate_statements_with_no_assert_to_z3<'a>(statements: &Vec<Statement>, ctx: &'a Context) -> Vec<Z3Ast<'a>> {
        let mut assume_conditions: Vec<Bool<'a>> = Vec::new();
    
        for statement in statements {
            match statement {
                Statement::Assume(expr) => {
                    let z3_expr = Self::translate_expr_to_z3(expr, ctx);
                    let assume_val = match &z3_expr {
                        Z3Ast::Bool(val) => val.clone(),
                        // handle other variants if necessary...
                        _ => panic!("Expected a boolean expression"),
                    };
                    assume_conditions.push(assume_val);
                }
                _ => {}
            }
        }
    
        // Combine all the Assume conditions.
        let combined_assume = assume_conditions.iter().fold(Bool::from_bool(ctx, true), |acc, x| Bool::and(ctx, &[&acc, x]));
        vec![Z3Ast::Bool(combined_assume)]
    }
    
}