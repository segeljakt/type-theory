// Derived from https://github.com/nwoeanhinnogaehr/algorithmw-rust
use {
    crate::ast::*,
    std::{
        collections::{HashMap as Map, HashSet as Set},
        result,
    },
};

type Result<T> = result::Result<T, TypeError>;

impl Subs {
    /// Construct an empty substitution.
    fn new() -> Subs {
        Subs(Map::new())
    }
    /// Union `s1` with `s2` and prefer element of `s1` in the case of collision.
    fn union(s1: &Subs, s2: &Subs) -> Self {
        let mut res = s1.clone();
        for (key, value) in &s2.0 {
            res.entry(key.clone()).or_insert(value.clone());
        }
        res
    }
    /// To compose two substitutions s1 and s2, we apply s1 to each
    /// type in s2 and union the resulting substitution with s1.
    fn compose(s1: Subs, s2: Subs) -> Subs {
        let s2 = Subs(
            s2.iter()
                .map(|(k, v)| (k.clone(), v.substitute(&s1)))
                .collect(),
        );
        Subs::union(&s1, &s2)
    }
}

trait TypeMethods {
    /// Returns the set of free type variables of self
    fn ftv(&self) -> Set<TypeName>;
    /// Applies a substitution to self
    fn substitute(&self, sub: &Subs) -> Self;
}

/// Unifies two types `ty1` and `ty2`
fn unify(ty1: &Type, ty2: &Type) -> Result<Subs> {
    match (ty1, ty2) {
        (Type::Var(name), ty) | (ty, Type::Var(name)) => {
            if ty.ftv().contains(name) {
                Err(TypeError(format!("`{}` and `{}` are recursive", ty1, ty2,)))
            } else {
                let mut sub = Subs::new();
                sub.insert(name.clone(), ty.clone());
                Ok(sub)
            }
        }
        (Type::Cons(name1, args1), Type::Cons(name2, args2)) => {
            if name1 != name2 || args1.len() != args2.len() {
                Err(TypeError(format!("Cannot unify `{}` with `{}`", ty1, ty2,)))
            } else {
                args1
                    .iter()
                    .zip(args2)
                    .try_fold(Subs::new(), |sub, (arg1, arg2)| {
                        let new_sub = unify(&arg1.substitute(&sub), &arg2.substitute(&sub))?;
                        Ok(Subs::compose(new_sub, sub))
                    })
            }
        }
        (Type::Error, _) | (_, Type::Error) => Ok(Subs::new()),
    }
}

static mut NEXT: usize = 0;

impl Type {
    pub fn new_var() -> Type {
        unsafe {
            let var = Type::Var(format!("'t{}", NEXT));
            NEXT += 1;
            var
        }
    }
}

impl TypeMethods for Type {
    // Return the set of free type variables in self
    fn ftv(&self) -> Set<TypeName> {
        match self {
            Type::Var(name) => {
                let mut set = Set::new();
                set.insert(name.clone());
                set
            }
            Type::Cons(_, args) => args.ftv(),
            Type::Error => Set::new(),
        }
    }

    // Substitute all type variables in `self` with `sub`
    fn substitute(&self, sub: &Subs) -> Type {
        match self {
            Type::Var(name) => sub.get(name).cloned().unwrap_or(self.clone()),
            Type::Cons(name, args) => Type::Cons(name.clone(), args.substitute(sub)),
            Type::Error => Type::Error,
        }
    }
}

/// Helper methods for Type and Scheme
impl<'a, T: TypeMethods> TypeMethods for Vec<T> {
    fn ftv(&self) -> Set<TypeName> {
        self.iter().fold(Set::new(), |set, ty| {
            set.union(&ty.ftv()).cloned().collect()
        })
    }

    fn substitute(&self, sub: &Subs) -> Vec<T> {
        self.iter().map(|ty| ty.substitute(sub)).collect()
    }
}

impl TypeMethods for Scheme {
    /// The free type variables in a scheme are those that are free
    /// in the internal type and not bound by the variable mapping.
    fn ftv(&self) -> Set<TypeName> {
        self.ty.ftv().difference(&self.vars).cloned().collect()
    }

    /// Substitutions are applied to free type variables only.
    fn substitute(&self, sub: &Subs) -> Scheme {
        Scheme::poly(
            self.vars.clone(),
            self.ty
                .substitute(&self.vars.iter().fold(sub.clone(), |mut sub, var| {
                    sub.remove(var);
                    sub
                })),
        )
    }
}

impl Scheme {
    /// Returns a polytype (Type with quantifiers)
    pub fn poly(vars: Set<TypeName>, ty: Type) -> Scheme {
        Scheme { ty, vars }
    }

    /// Returns a monotype (Type with without quantifiers)
    pub fn mono(ty: Type) -> Scheme {
        Scheme {
            ty,
            vars: Set::new(),
        }
    }
    /// Instantiates a scheme into a type. Replaces all bound type variables with fresh type
    /// variables and return the resulting type.
    fn instantiate(&self) -> Type {
        self.ty.substitute(&Subs(
            self.vars
                .iter()
                .cloned()
                .zip(self.vars.iter().map(|_| Type::new_var()))
                .collect(),
        ))
    }
}

impl TypeMethods for Env {
    /// The free type variables of a type environment is the union
    /// of the free type variables of each scheme in the environment.
    fn ftv(&self) -> Set<TypeName> {
        self.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    /// To apply a substitution, we just apply it to each scheme in the type environment.
    fn substitute(&self, sub: &Subs) -> Env {
        Env(self
            .iter()
            .map(|(k, v)| (k.clone(), v.substitute(sub)))
            .collect())
    }
}

impl Env {
    /// Construct an empty type environment.
    pub fn new() -> Env {
        Env(Map::new())
    }

    /// Generalize creates a scheme
    fn generalize(&self, ty: &Type) -> Scheme {
        Scheme {
            vars: ty.ftv().difference(&self.ftv()).cloned().collect(),
            ty: ty.clone(),
        }
    }

    fn infer(&self, exp: &Exp) -> Result<(Type, Subs)> {
        match exp {
            Exp::Var(name) => self
                .get(name)
                .map(|scheme| (scheme.instantiate(), Subs::new()))
                .ok_or_else(|| TypeError(format!("Cannot reference unbound variable: {}", name))),
            Exp::Lit(lit) => match lit {
                Lit::Int(_) => Ok((Type::int(), Subs::new())),
                Lit::Bool(_) => Ok((Type::bool(), Subs::new())),
                Lit::Str(_) => Ok((Type::str(), Subs::new())),
            },
            Exp::Abs(name, expr) => {
                let ty_arg = Type::new_var();
                let mut env = self.clone();
                env.insert(name.clone(), Scheme::mono(ty_arg.clone()));
                let (ty_ret, s1) = env.infer(expr)?;
                let ty_arg = ty_arg.substitute(&s1);
                let ty_fun = Type::fun(ty_arg, ty_ret);
                Ok((ty_fun, s1))
            }
            Exp::App(fun, arg) => {
                let (ty_fun, s1) = self.infer(fun)?;
                let (ty_arg, s2) = self.substitute(&s1).infer(arg)?;
                let ty_ret = Type::new_var();
                let ty_fun = ty_fun.substitute(&s2);
                let s3 = unify(&ty_fun, &Type::fun(ty_arg, ty_ret.clone()))?;
                let ty_ret = ty_ret.substitute(&s3);
                Ok((ty_ret, Subs::compose(s3, Subs::compose(s2, s1))))
            }
            Exp::Let(name, arg, body) => {
                let mut env = self.clone();
                env.remove(name);
                let (ty_arg, s1) = self.infer(arg)?;
                let scheme = env.substitute(&s1).generalize(&ty_arg);
                env.insert(name.clone(), scheme);
                let (ty_body, s2) = env.substitute(&s1).infer(body)?;
                Ok((ty_body, Subs::compose(s2, s1)))
            }
            Exp::Error => Ok((Type::Error, Subs::new())),
        }
    }

    /// Perform type inference on an expression and return the resulting type, if any.
    pub fn infer_type(&self, exp: &Exp) -> Result<Type> {
        unsafe {
            NEXT = 0;
        }
        let (ty, s) = self.infer(exp)?;
        Ok(ty.substitute(&s))
    }
}
