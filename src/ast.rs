use {newtype::NewType, std::collections::HashMap};

pub type Name = String;
pub type TermName = String;
pub type TypeName = String;

#[derive(Debug)]
pub enum Exp {
    Var(TermName),
    Lit(Lit),
    App(Box<Exp>, Box<Exp>),
    Abs(TermName, Box<Exp>),
    Let(TermName, Box<Exp>, Box<Exp>),
    Error,
}

#[derive(Debug)]
pub enum Lit {
    Int(i64),
    Bool(bool),
    Str(String),
}

#[derive(Clone, Debug)]
pub enum Type {
    Var(TypeName),
    Con(TypeName, Vec<Type>),
    Error,
}

#[derive(Clone, Debug)]
pub struct Scheme {
    pub vars: Vec<TypeName>,
    pub ty: Type,
}

#[derive(Clone, Debug, NewType)]
pub struct Info(HashMap<TypeName, String>);

#[derive(Clone, Debug, NewType)]
pub struct Sub(pub HashMap<TypeName, Type>);

#[derive(Clone, Debug, NewType)]
pub struct Ctx(pub HashMap<TermName, Scheme>);

pub struct LambdaType;

impl LambdaType {
    pub fn int() -> String {
        "int".to_owned()
    }
    pub fn bool() -> String {
        "bool".to_owned()
    }
    pub fn str() -> String {
        "str".to_owned()
    }
    pub fn fun() -> String {
        "->".to_owned()
    }
}

#[derive(Debug)]
pub struct TypeError(pub String);
