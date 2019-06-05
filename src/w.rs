// Derived from https://github.com/nwoeanhinnogaehr/algorithmw-rust
use {
    crate::ast::*,
    std::{
        collections::{HashMap, HashSet},
        hash::Hash,
        result,
    },
};

trait Union {
    fn union(&self, other: &Self) -> Self;
}

/// Implement union for HashMap such that the value in `self` is used over the value in `other` in
/// the event of a collision.
impl<K, V> Union for HashMap<K, V>
where
    K: Clone + Eq + Hash,
    V: Clone,
{
    fn union(&self, other: &Self) -> Self {
        let mut res = self.clone();
        for (key, value) in other {
            res.entry(key.clone()).or_insert(value.clone());
        }
        res
    }
}

type Result<T> = result::Result<T, TypeError>;

trait TypeMethods {
    fn ftv(&self) -> HashSet<TypeName>;
    fn apply(&self, sub: &Sub) -> Self;
}

impl<'a, T: TypeMethods> TypeMethods for Vec<T> {
    fn ftv(&self) -> HashSet<TypeName> {
        self.iter().fold(HashSet::new(), |set, ty| {
            set.union(&ty.ftv()).cloned().collect()
        })
    }

    fn apply(&self, sub: &Sub) -> Vec<T> {
        self.iter().map(|ty| ty.apply(sub)).collect()
    }
}

fn unify(ty1: &Type, ty2: &Type) -> Result<Sub> {
    match (ty1, ty2) {
        (Type::Var(name), ty) | (ty, Type::Var(name)) => {
            if ty.ftv().contains(name) {
                Err(TypeError(format!("`{}` and `{}` are recursive", ty1, ty2,)))
            } else {
                let mut sub = Sub::new();
                sub.insert(name.clone(), ty.clone());
                Ok(sub)
            }
        }
        (Type::Con(name1, args1), Type::Con(name2, args2)) => {
            if name1 != name2 || args1.len() != args2.len() {
                Err(TypeError(format!("Cannot unify `{}` with `{}`", ty1, ty2,)))
            } else {
                args1
                    .iter()
                    .zip(args2)
                    .try_fold(Sub::new(), |sub, (arg1, arg2)| {
                        let new_sub = unify(&arg1.apply(&sub), &arg2.apply(&sub))?;
                        Ok(compose(new_sub, sub))
                    })
            }
        }
        (Type::Error, _) | (_, Type::Error) => Ok(Sub::new()),
    }
}

static mut NEXT: usize = 0;

impl Type {
    pub fn new_var() -> Type {
        unsafe {
            let var = Type::Var(format!("{}", NEXT));
            NEXT += 1;
            var
        }
    }
}

impl TypeMethods for Type {
    fn ftv(&self) -> HashSet<TypeName> {
        match self {
            Type::Var(name) => {
                let mut set = HashSet::new();
                set.insert(name.clone());
                set
            }
            Type::Con(_, args) => args.iter().fold(HashSet::new(), |set, arg| {
                set.union(&arg.ftv()).cloned().collect()
            }),
            Type::Error => HashSet::new()
        }
    }

    fn apply(&self, sub: &Sub) -> Type {
        match self {
            Type::Var(name) => sub.get(name).cloned().unwrap_or(self.clone()),
            Type::Con(name, args) => Type::Con(
                name.clone(),
                args.iter().cloned().map(|arg| arg.apply(sub)).collect(),
            ),
            Type::Error => Type::Error
        }
    }
}

impl TypeMethods for Scheme {
    /// The free type variables in a scheme are those that are free in the internal type and not
    /// bound by the variable mapping.
    fn ftv(&self) -> HashSet<TypeName> {
        self.ty
            .ftv()
            .difference(&self.vars.iter().cloned().collect())
            .cloned()
            .collect()
    }

    /// Substitutions are applied to free type variables only.
    fn apply(&self, sub: &Sub) -> Scheme {
        Scheme::poly(
            self.vars.clone(),
            self.ty
                .apply(&self.vars.iter().fold(sub.clone(), |mut sub, var| {
                    sub.remove(var);
                    sub
                })),
        )
    }
}

impl Scheme {
    pub fn poly(vars: Vec<TypeName>, ty: Type) -> Scheme {
        Scheme { ty, vars }
    }
    pub fn mono(ty: Type) -> Scheme {
        Scheme {
            ty,
            vars: Vec::new(),
        }
    }
    /// Instantiates a scheme into a type. Replaces all bound type variables with fresh type
    /// variables and return the resulting type.
    fn instantiate(&self) -> Type {
        let newvars = self.vars.iter().map(|_| Type::new_var());
        self.ty
            .apply(&Sub(self.vars.iter().cloned().zip(newvars).collect()))
    }
}

impl Sub {
    /// Construct an empty substitution.
    fn new() -> Sub {
        Sub(HashMap::new())
    }
}

/// To compose two substitutions, we apply self to each type in other and union the resulting
/// substitution with self.
fn compose(s1: Sub, s2: Sub) -> Sub {
    Sub(s1.union(&s2.iter().map(|(k, v)| (k.clone(), v.apply(&s1))).collect()))
}

impl TypeMethods for Ctx {
    /// The free type variables of a type environment is the union of the free type variables of
    /// each scheme in the environment.
    fn ftv(&self) -> HashSet<TypeName> {
        self.values()
            .map(|x| x.clone())
            .collect::<Vec<Scheme>>()
            .ftv()
    }

    /// To apply a substitution, we just apply it to each scheme in the type environment.
    fn apply(&self, sub: &Sub) -> Ctx {
        Ctx(self
            .iter()
            .map(|(k, v)| (k.clone(), v.apply(sub)))
            .collect())
    }
}

impl Ctx {
    /// Construct an empty type environment.
    pub fn new() -> Ctx {
        Ctx(HashMap::new())
    }

    /// Generalize creates a scheme
    fn generalize(&self, ty: &Type) -> Scheme {
        Scheme {
            vars: ty.ftv().difference(&self.ftv()).cloned().collect(),
            ty: ty.clone(),
        }
    }

    fn infer(&self, exp: &Exp) -> Result<(Type, Sub)> {
        match exp {
            Exp::Var(name) => match self.get(name) {
                Some(scheme) => Ok((scheme.instantiate(), Sub::new())),
                None => Err(TypeError(format!(
                    "Cannot reference unbound variable: {}",
                    name
                ))),
            },
            Exp::Lit(lit) => {
                let name = match lit {
                    Lit::Int(_) => LambdaType::int(),
                    Lit::Bool(_) => LambdaType::bool(),
                    Lit::Str(_) => LambdaType::str(),
                };
                let ty = Type::Con(name, Vec::new());
                Ok((ty, Sub::new()))
            }
            Exp::Abs(name, expr) => {
                let ty_arg = Type::new_var();
                let mut env = self.clone();
                env.insert(name.clone(), Scheme::mono(ty_arg.clone()));
                let (ty_ret, s1) = env.infer(expr)?;
                let ty_arg = ty_arg.apply(&s1);
                let ty_fun = Type::Con(LambdaType::fun(), vec![ty_arg, ty_ret]);
                Ok((ty_fun, s1))
            }
            Exp::App(fun, arg) => {
                let (ty_fun, s1) = self.infer(fun)?;
                let (ty_arg, s2) = self.apply(&s1).infer(arg)?;
                let ty_ret = Type::new_var();
                let ty_fun = ty_fun.apply(&s2);
                let s3 = unify(
                    &ty_fun,
                    &Type::Con(LambdaType::fun(), vec![ty_arg, ty_ret.clone()]),
                )?;
                let ty_ret = ty_ret.apply(&s3);
                Ok((ty_ret, compose(s3, compose(s2, s1))))
            }
            Exp::Let(name, expr, body) => {
                let mut env = self.clone();
                env.remove(name);
                let (ty_expr, s1) = self.infer(expr)?;
                let scheme = env.apply(&s1).generalize(&ty_expr);
                env.insert(name.clone(), scheme);
                let (ty_body, s2) = env.apply(&s1).infer(body)?;
                Ok((ty_body, compose(s2, s1)))
            }
            Exp::Error => Ok((Type::Error, Sub::new())),
        }
    }

    /// Perform type inference on an expression and return the resulting type, if any.
    pub fn infer_type(&self, exp: &Exp) -> Result<Type> {
        unsafe {
            NEXT = 0;
        }
        let (t, s) = self.infer(exp)?;
        Ok(t.apply(&s))
    }
}
