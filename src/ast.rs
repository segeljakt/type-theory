use newtype::NewType;
pub use smartstring::alias::String as Name;
pub use std::collections::{HashMap as Map, HashSet as Set};

/// An expression
#[derive(Debug)]
pub enum Exp {
    /// Variable
    Var(Name),
    /// Literal
    Lit(Lit),
    /// Application
    App(Box<Exp>, Box<Exp>),
    /// Abstraction
    Abs(Name, Box<Exp>),
    /// Let-binding
    Let(Name, Box<Exp>, Box<Exp>),
    /// An error
    Error,
}

/// A literal
#[derive(Debug)]
pub enum Lit {
    /// An integer
    Int(i64),
    /// A boolean
    Bool(bool),
    /// A string
    Str(String),
}

#[derive(Clone, Debug)]
pub enum Type {
    /// Variable type (Name is free)
    Var(Name),
    /// Constructed type (Name is bound)
    Cons(Name, Vec<Type>),
    /// An error
    Error,
}

#[derive(Clone, Debug)]
pub enum Scheme {
    /// A polytype is a type which contains a set of forall quantifiers
    Poly(Type, Set<Name>),
    /// A monotype is a type which does not have any quantifiers
    Mono(Type),
}

/// An environment mapping type-variables to types.
#[derive(Clone, Debug, NewType)]
pub struct Env(pub Map<Name, Type>);

/// A type variable generator.
#[derive(Clone, Debug, NewType)]
pub struct Gen(pub usize);

/// An environment mapping term-variables (functions) to schemes.
#[derive(Clone, Debug, NewType)]
pub struct Ctx(pub Map<Name, Scheme>);

impl Type {
    pub fn int() -> Type {
        Type::Cons("int".into(), vec![])
    }
    pub fn bool() -> Type {
        Type::Cons("bool".into(), vec![])
    }
    pub fn str() -> Type {
        Type::Cons("str".into(), vec![])
    }
    pub fn fun(arg: Type, ret: Type) -> Type {
        Type::Cons("->".into(), vec![arg, ret])
    }
}

#[derive(Debug)]
pub struct TypeError(pub String);
