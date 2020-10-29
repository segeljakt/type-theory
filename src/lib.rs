pub mod ast;
pub mod conversion;
pub mod display;
pub mod w;
pub mod wand;

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

    let mut ctx = Env::new();
    for (name, scheme) in funs {
        ctx.insert(name, scheme);
    }

    println!("{}", ctx);
    for exp in exps {
        println!("{}", exp);
        match exp.infer_w(&ctx) {
            Err(e) => eprintln!("[W] Error: {}", e),
            Ok(ty) => println!("[W] Inferred type: {}", ty),
        }
        println!("");
    }
    Ok(())
}
