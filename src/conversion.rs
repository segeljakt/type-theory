use crate::ast::Lit;

// Conversion functions
impl From<i64> for Lit {
    fn from(x: i64) -> Lit {
        Lit::Int(x)
    }
}

impl From<bool> for Lit {
    fn from(x: bool) -> Lit {
        Lit::Bool(x)
    }
}

impl<'a> From<&'a str> for Lit {
    fn from(x: &str) -> Lit {
        Lit::Str(x.into())
    }
}
