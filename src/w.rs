// Derived from https://github.com/nwoeanhinnogaehr/algorithmw-rust
use {crate::ast::*, std::result};

type Result<T> = result::Result<T, TypeError>;

impl Env {
    /// Construct an empty environment.
    fn new() -> Self {
        Env(Map::new())
    }
    /// Union `env1` with `env2` and prefer elements of `env1` in the case of collision.
    fn union(env1: Env, env2: Env) -> Self {
        let mut res = env1.clone();
        for (name, ty) in &env2.0 {
            res.entry(name.clone()).or_insert(ty.clone());
        }
        res
    }
    /// Composes two environments `env1` and `env2` by applying the substitutions
    /// in `env1` to each type in `env2` and unions the resulting environment with `env1`.
    fn compose(env1: Env, env2: Env) -> Self {
        let env2 = Env(env2
            .iter()
            .map(|(name, ty)| (name.clone(), ty.substitute(&env1)))
            .collect());
        Env::union(env1, env2)
    }
}

trait TypeMethods {
    /// Returns the set of free type variables of self
    fn ftv(&self) -> Set<Name>;
    /// Applies a substitution to self
    fn substitute(&self, env: &Env) -> Self;
}

/// Unifies two types `ty1` and `ty2`
fn unify(ty1: &Type, ty2: &Type) -> Result<Env> {
    match (ty1, ty2) {
        (Type::Var(name), ty) | (ty, Type::Var(name)) => {
            if ty.ftv().contains(name) {
                Err(TypeError(format!("`{}` and `{}` are recursive", ty1, ty2)))
            } else {
                let mut env = Env::new();
                env.insert(name.clone(), ty.clone());
                Ok(env)
            }
        }
        (Type::Cons(name1, params1), Type::Cons(name2, params2)) => {
            if name1 != name2 || params1.len() != params2.len() {
                Err(TypeError(format!("Cannot unify `{}` with `{}`", ty1, ty2,)))
            } else {
                params1
                    .iter()
                    .zip(params2)
                    .try_fold(Env::new(), |env, (arg1, arg2)| {
                        let new_env = unify(&arg1.substitute(&env), &arg2.substitute(&env))?;
                        Ok(Env::compose(new_env, env))
                    })
            }
        }
        (Type::Error, _) | (_, Type::Error) => Ok(Env::new()),
    }
}

impl Gen {
    pub fn new() -> Self {
        Gen(0)
    }
    pub fn fresh(&mut self) -> Type {
        let var = Type::Var(format!("'t{}", self.0).into());
        self.0 += 1;
        var
    }
}

impl TypeMethods for Type {
    // Return the set of all (free) Type::Var in self
    fn ftv(&self) -> Set<Name> {
        match self {
            Type::Var(name) => {
                let mut set = Set::new();
                set.insert(name.clone());
                set
            }
            Type::Cons(_, params) => params.ftv(),
            Type::Error => Set::new(),
        }
    }

    // Substitute all type variables in `self` with `env`
    fn substitute(&self, env: &Env) -> Type {
        match self {
            Type::Var(name) => env.get(name).cloned().unwrap_or(self.clone()),
            Type::Cons(name, params) => Type::Cons(name.clone(), params.substitute(env)),
            Type::Error => Type::Error,
        }
    }
}

/// Helper methods for Type and Scheme
impl<'a, T: TypeMethods> TypeMethods for Vec<T> {
    fn ftv(&self) -> Set<Name> {
        self.iter().fold(Set::new(), |set, ty| {
            set.union(&ty.ftv()).cloned().collect()
        })
    }

    fn substitute(&self, env: &Env) -> Vec<T> {
        self.iter().map(|ty| ty.substitute(env)).collect()
    }
}

impl TypeMethods for Scheme {
    /// The free type variables in a scheme are those that are free
    /// in the internal type and not bound by the variable mapping.
    fn ftv(&self) -> Set<Name> {
        match self {
            Scheme::Mono(ty) => ty.ftv(),
            Scheme::Poly(ty, quantifiers) => ty.ftv().difference(&quantifiers).cloned().collect(),
        }
    }

    /// Substitutions are applied to free type variables only.
    fn substitute(&self, env: &Env) -> Scheme {
        match self {
            Scheme::Mono(ty) => Scheme::Mono(ty.substitute(env)),
            Scheme::Poly(ty, quantifiers) => Scheme::Poly(
                ty.substitute(&quantifiers.iter().fold(env.clone(), |mut env, var| {
                    env.remove(var);
                    env
                })),
                quantifiers.clone(),
            ),
        }
    }
}

impl TypeMethods for Ctx {
    /// The free type variables of a context is the union
    /// of the free type variables of each scheme in the context.
    fn ftv(&self) -> Set<Name> {
        self.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    /// To apply a substitution, we just apply it to each scheme in the type environment.
    fn substitute(&self, env: &Env) -> Ctx {
        Ctx(self
            .iter()
            .map(|(name, scheme)| (name.clone(), scheme.substitute(env)))
            .collect())
    }
}

impl Ctx {
    /// Construct an empty type context.
    pub fn new() -> Ctx {
        Ctx(Map::new())
    }
}

impl Scheme {
    /// Specialises a scheme into a type by replacing all quantifiers
    /// with fresh type variables.
    fn specialise(&self, gen: &mut Gen) -> Type {
        match self {
            Scheme::Mono(ty) => ty.clone(),
            Scheme::Poly(ty, quantifiers) => ty.substitute(&Env(quantifiers
                .iter()
                .cloned()
                .zip(quantifiers.iter().map(|_| gen.fresh()))
                .collect())),
        }
    }
}

impl Type {
    /// Generalises a type into a scheme by quantifying over
    /// all free variables in the type.
    fn generalise(self: &Type, ctx: &Ctx) -> Scheme {
        let quantifiers = self
            .ftv()
            .difference(&ctx.ftv())
            .cloned()
            .collect::<Set<Name>>();
        if !quantifiers.is_empty() {
            Scheme::Poly(self.clone(), quantifiers)
        } else {
            Scheme::Mono(self.clone())
        }
    }
}

impl Exp {
    /// Perform type inference on an expression and return the resulting type, if any.
    pub fn infer_type(&self, ctx: &Ctx) -> Result<Type> {
        let mut gen = Gen::new();
        let (ty, env) = self.infer(ctx, &mut gen)?;
        Ok(ty.substitute(&env))
    }

    fn infer(&self, ctx: &Ctx, gen: &mut Gen) -> Result<(Type, Env)> {
        match self {
            Exp::Var(name) => ctx
                .get(name)
                .map(|scheme| (scheme.specialise(gen), Env::new()))
                .ok_or_else(|| TypeError(format!("Cannot reference unbound variable: {}", name))),
            Exp::Lit(lit) => match lit {
                Lit::Int(_) => Ok((Type::int(), Env::new())),
                Lit::Bool(_) => Ok((Type::bool(), Env::new())),
                Lit::Str(_) => Ok((Type::str(), Env::new())),
            },
            Exp::Abs(name, body) => {
                let ty_arg = gen.fresh();
                let mut ctx = ctx.clone();
                ctx.insert(name.clone(), Scheme::Mono(ty_arg.clone()));
                let (ty_ret, env1) = body.infer(&ctx, gen)?;
                let ty_arg = ty_arg.substitute(&env1);
                let ty_fun = Type::fun(ty_arg, ty_ret);
                Ok((ty_fun, env1))
            }
            Exp::App(fun, arg) => {
                let (ty_fun, env1) = fun.infer(ctx, gen)?;
                let (ty_arg, env2) = arg.infer(&ctx.substitute(&env1), gen)?;
                let ty_ret = gen.fresh();
                let ty_fun = ty_fun.substitute(&env2);
                let env3 = unify(&ty_fun, &Type::fun(ty_arg, ty_ret.clone()))?;
                let ty_ret = ty_ret.substitute(&env3);
                Ok((ty_ret, Env::compose(env3, Env::compose(env2, env1))))
            }
            Exp::Let(name, arg, body) => {
                let mut ctx = ctx.clone();
                ctx.remove(name);
                let (ty_arg, env1) = arg.infer(&ctx, gen)?;
                let scheme = ty_arg.generalise(&ctx.substitute(&env1));
                ctx.insert(name.clone(), scheme);
                let (ty_body, env2) = body.infer(&ctx.substitute(&env1), gen)?;
                Ok((ty_body, Env::compose(env2, env1)))
            }
            Exp::Error => Ok((Type::Error, Env::new())),
        }
    }
}
