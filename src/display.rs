use {crate::ast::*, std::fmt};
use crate::ast::result::*;

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Exp::Var(name) => write!(f, "{}", name),
            Exp::Lit(lit) => write!(f, "{}", lit),
            Exp::App(fun, arg) => write!(f, "({} {})", fun, arg),
            Exp::Abs(name, body) => write!(f, "λ{}.{}", name, body),
            Exp::Let(name, rhs, body) => write!(f, "let {} = {} in {}", name, rhs, body),
            Exp::LetRec(name, rhs, body) => write!(f, "let rec {} = {} in {}", name, rhs, body),
            Exp::Error => write!(f, "<error>"),
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Lit::Int(val) => write!(f, "{}", val),
            Lit::Bool(val) => write!(f, "{}", val),
            Lit::Str(val) => write!(f, "{}", val),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(name) => write!(f, "{}", name),
            Type::Cons(name, params) if name == "->" && params.len() == 2 => {
                write!(f, "({} → {})", params[0], params[1])
            }
            Type::Cons(name, params) if params.len() > 0 => {
                let args = params
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<String>>()
                    .join(",");
                write!(f, "{}[{}]", name, args)
            }
            Type::Cons(name, _) => write!(f, "{}", name),
            Type::Error => write!(f, "<error>"),
        }
    }
}

impl fmt::Display for TypeError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let TypeError(msg) = self;
        write!(f, "{}", msg)
    }
}

impl std::error::Error for TypeError {}

impl fmt::Display for Env<Type> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[")?;
        for (key, val) in self.iter() {
            writeln!(f, "  {} => {},", key, val)?;
        }
        writeln!(f, "]")
    }
}

impl fmt::Display for Env<Scheme> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (key, scheme) in self.iter() {
            match scheme {
                Scheme::Poly(ty, quantifiers) => {
                    let quantifiers = quantifiers
                        .iter()
                        .map(|name| name.to_string())
                        .collect::<Vec<String>>()
                        .join(" ");
                    writeln!(f, "{} :: ∀ {} . {}", key, quantifiers, ty)?;
                }
                Scheme::Mono(ty) => {
                    writeln!(f, "{} :: {}", key, ty)?;
                }
            }
        }
        Ok(())
    }
}
