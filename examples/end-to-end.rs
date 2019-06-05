use type_theory::*;
fn main() -> std::io::Result<()> {
    compile(include_str!("code.λ").to_owned()).unwrap();
    Ok(())
}
