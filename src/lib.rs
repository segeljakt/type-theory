pub mod ast;
pub mod conversion;
pub mod display;
pub mod w;

use {
    crate::ast::*,
    lalrpop_util::lalrpop_mod,
    std::{fs::File, io::prelude::*},
};

lalrpop_mod!(pub parser);

pub fn compile_file(path: &str) -> Result<(), Box<dyn std::error::Error + 'static>> {
    let mut file = File::open(path)?;
    let mut source = String::new();
    file.read_to_string(&mut source)?;
    compile(source)?;
    Ok(())
}

pub fn compile(source: String) -> Result<(), Box<dyn std::error::Error + 'static>> {
    let mut errors = Vec::new();
    let (funs, exps) = parser::ProgramParser::new().parse(&mut errors, &source).unwrap();

    let mut ctx = Ctx::new();
    for (name, scheme) in funs {
        ctx.insert(name, scheme);
    }

    println!("{}", ctx);
    for exp in exps {
        println!("{}", exp);
        match ctx.infer_type(&exp) {
            Err(e) => eprintln!("Error: {}", e),
            Ok(ty) => println!("Inferred type: {}", ty),
        }
        println!("");
    }
    Ok(())
}
