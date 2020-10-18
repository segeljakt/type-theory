pub mod ast;
pub mod conversion;
pub mod display;
pub mod w;

use {
    crate::ast::*,
    lalrpop_util::lalrpop_mod,
    std::{fs::File, io::prelude::*},
};

lalrpop_mod!(#[allow(unused_parens)] #[clippy::ignore] pub parser);

pub fn compile_file(path: &str) -> Result<(), Box<dyn std::error::Error + 'static>> {
    let mut file = File::open(path)?;
    let mut source = String::new();
    file.read_to_string(&mut source)?;
    compile(source)?;
    Ok(())
}

pub fn compile(source: String) -> Result<(), Box<dyn std::error::Error + 'static>> {
    let mut errors = Vec::new();
    let (funs, exps) = parser::ProgramParser::new()
        .parse(&mut errors, &source)
        .unwrap();

    let mut env = Env::new();
    for (name, scheme) in funs {
        env.insert(name, scheme);
    }

    println!("{}", env);
    for exp in exps {
        println!("{}", exp);
        match exp.infer_type(&env) {
            Err(e) => eprintln!("Error: {}", e),
            Ok(ty) => println!("Inferred type: {}", ty),
        }
        println!("");
    }
    Ok(())
}
