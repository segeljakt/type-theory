use {crate::ast::*, std::fmt};

impl fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Exp::Var(x) => write!(f, "{}", x),
            Exp::Lit(x) => write!(f, "{}", x),
            Exp::App(e1, e2) => write!(f, "({} {})", e1, e2),
            Exp::Abs(i, e) => write!(f, "λ{}.{}", i, e),
            Exp::Let(i, e1, e2) => write!(f, "let {} = {} in {}", i, e1, e2),
            Exp::Error => write!(f, "<error>"),
        }
    }
}

impl fmt::Display for Lit {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Lit::Int(x) => write!(f, "{}", x),
            Lit::Bool(x) => write!(f, "{}", x),
            Lit::Str(x) => write!(f, "{:?}", x),
        }
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Type::Var(x) => write!(f, "'t{}", x),
            Type::Con(name, args) if *name == LambdaType::fun() && args.len() == 2 => {
                write!(f, "({} → {})", args[0], args[1])
            }
            Type::Con(name, args) if args.len() > 0 => {
                let args = args
                    .iter()
                    .map(|arg| arg.to_string())
                    .collect::<Vec<String>>()
                    .join(",");
                write!(f, "{}[{}]", name, args)
            }
            Type::Con(name, _) => write!(f, "{}", name),
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

impl fmt::Display for Sub {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "[")?;
        for (key, val) in self.iter() {
            writeln!(f, "  {} => {},", key, val)?;
        }
        writeln!(f, "]")
    }
}

impl fmt::Display for Ctx {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (key, Scheme { vars, ty }) in self.iter() {
            if vars.len() > 0 {
                let vars = vars
                    .iter()
                    .map(|v| v.to_string())
                    .collect::<Vec<String>>()
                    .join(" ");
                writeln!(f, "{} :: ∀ {} . {}", key, vars, ty)?;
            } else {
                writeln!(f, "{} :: {}", key, ty)?;
            }
        }
        Ok(())
    }
}
