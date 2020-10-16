use {
    newtype::NewType,
    std::collections::{HashMap as Map, HashSet as Set},
};

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
    /// Unbound type (TypeName is free)
    Var(TypeName),
    /// Constructed type (TypeName is bound)
    Cons(TypeName, Vec<Type>),
    Error,
}

#[derive(Clone, Debug)]
pub struct Scheme {
    pub vars: Set<TypeName>,
    pub ty: Type,
}

#[derive(Clone, Debug, NewType)]
pub struct Info(Map<TypeName, String>);

#[derive(Clone, Debug, NewType)]
pub struct Subs(pub Map<TypeName, Type>);

#[derive(Clone, Debug, NewType)]
pub struct Gen(pub usize);

#[derive(Clone, Debug, NewType)]
pub struct Env(pub Map<TermName, Scheme>);

impl Type {
    pub fn int() -> Type {
        Type::Cons("int".to_owned(), vec![])
    }
    pub fn bool() -> Type {
        Type::Cons("bool".to_owned(), vec![])
    }
    pub fn str() -> Type {
        Type::Cons("str".to_owned(), vec![])
    }
    pub fn fun(arg: Type, ret: Type) -> Type {
        Type::Cons("->".to_owned(), vec![arg, ret])
    }
}

#[derive(Debug)]
pub struct TypeError(pub String);
