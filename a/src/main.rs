use miette::Result;
pub use syntax::{self, ast};

fn main() -> Result<()> {
    // Parsing example
    for p in std::env::args().skip(1) {
        let doc_ast = syntax::parse_file(p)?;
        println!("{doc_ast:#?}");

        let new_doc_ast = syntax::encode1(doc_ast.clone())?;
        println!("{new_doc_ast:#?}");

        let new_new_doc_ast = syntax::encode2(new_doc_ast.clone())?;
        println!("{new_new_doc_ast:#?}");

    }

    // Z3 usage example
    use z3::{ast::Int, SatResult};

    let cfg = z3::Config::new();
    let ctx = z3::Context::new(&cfg);
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

// pub fn encode2ivl1(mut doc: Document) -> Result<Document, ParseError> {

//     for item in &mut doc.items {
//         if let DocumentItem::Method(method) = item {
//             if let Some(body) = &mut method.body {
//                 for input_var in &method.inputs {
//                     let var_decl = Statement::Var(input_var.clone(), None);
//                     body.statements.insert(0, var_decl);
//                 }
//             }
//         }
//     }
//     println!("{doc:#?}");
//     Ok(doc)
// }