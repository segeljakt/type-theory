// Derived from https://github.com/nwoeanhinnogaehr/algorithmw-rust
use {crate::ast::*, std::result};

type Result<T> = result::Result<T, TypeError>;

impl<T: std::fmt::Debug + Clone> Env<T> {
    /// Construct an empty environment.
    pub fn new() -> Self {
        Self(Map::new())
    }
    /// Union `self` with `other` and prefer elements of `self` in the case of collision.
    fn union(self, other: Self) -> Self {
        Self(self.0.into_iter().chain(other.0).collect())
    }
}

trait TypeMethods {
    /// Returns the set of free type variables of self
    fn ftv(&self) -> Set<Name>;
    /// Applies a substitution to self
    fn substitute(&self, env: &Env<Type>) -> Self;
}

/// Computes the most general unifier of two types `ty1` and `ty2`
fn mgu(ty1: &Type, ty2: &Type) -> Result<Env<Type>> {
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
                Err(TypeError(format!("Cannot unify `{}` with `{}`", ty1, ty2)))
            } else {
                params1
                    .iter()
                    .zip(params2)
                    .try_fold(Env::new(), |env0, (arg1, arg2)| {
                        let env1 = mgu(&arg1.substitute(&env0), &arg2.substitute(&env0))?;
                        Ok(env1.substitute(&env0))
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
    fn substitute(&self, env: &Env<Type>) -> Type {
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

    fn substitute(&self, env: &Env<Type>) -> Vec<T> {
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
    fn substitute(&self, env: &Env<Type>) -> Scheme {
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

impl TypeMethods for Env<Type> {
    fn ftv(&self) -> Set<Name> {
        self.values().cloned().collect::<Vec<Type>>().ftv()
    }
    fn substitute(&self, env: &Env<Type>) -> Self {
        let env = Env(env
            .iter()
            .map(|(name, ty)| (name.clone(), ty.substitute(self)))
            .collect());
        self.clone().union(env)
    }
}

impl TypeMethods for Env<Scheme> {
    /// The free type variables of a context is the union
    /// of the free type variables of each scheme in the context.
    fn ftv(&self) -> Set<Name> {
        self.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    /// To apply a substitution, we just apply it to each scheme in the type environment.
    fn substitute(&self, env: &Env<Type>) -> Env<Scheme> {
        Env(self
            .iter()
            .map(|(name, scheme)| (name.clone(), scheme.substitute(env)))
            .collect())
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
    fn generalise(self: &Type, ctx: &Env<Scheme>) -> Scheme {
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
    pub fn infer_type(&self, ctx: &Env<Scheme>) -> Result<Type> {
        let mut gen = Gen::new();
        let (ty, env) = self.infer(ctx, &mut gen)?;
        Ok(ty.substitute(&env))
    }

    fn infer(&self, ctx: &Env<Scheme>, gen: &mut Gen) -> Result<(Type, Env<Type>)> {
        match self {
            Exp::Lit(lit) => match lit {
                Lit::Int(_) => Ok((Type::int(), Env::new())),
                Lit::Bool(_) => Ok((Type::bool(), Env::new())),
                Lit::Str(_) => Ok((Type::str(), Env::new())),
            },
            //      x:σ ∈ Γ   t = specialise(σ)
            // (Var)---------------------------
            //            Γ ⊢ x:t,∅
            Exp::Var(name) => ctx
                .get(name)
                .map(|scheme| (scheme.specialise(gen), Env::new()))
                .ok_or_else(|| {
                    TypeError(format!("Term is not closed, found free variable: {}", name))
                }),
            //      t = fresh()   Γ,x:t ⊢ e:t',S
            // (Abs)----------------------------
            //          Γ ⊢ λx.e:St → t',S
            Exp::Abs(name, body) => {
                let ty_arg = gen.fresh();
                let mut ctx = ctx.clone();
                ctx.insert(name.clone(), Scheme::Mono(ty_arg.clone()));
                let (ty_ret, env0) = body.infer(&ctx, gen)?;
                let ty_arg = ty_arg.substitute(&env0);
                let ty_fun = Type::fun(ty_arg, ty_ret);
                Ok((ty_fun, env0))
            }
            //      Γ ⊢ e₀:t₀,S₀   S₀Γ ⊢ e₁:t₁,S₁   t' = fresh()   S₂ = mgu(S₁t₀, t₁ → t')
            // (App)------------------------------------------------------------------------
            //                                 Γ ⊢ e₀e₁:S₂t',S₂S₁S₀
            Exp::App(fun, arg) => {
                let (ty_fun, env0) = fun.infer(ctx, gen)?;
                let (ty_arg, env1) = arg.infer(&ctx.substitute(&env0), gen)?;
                let ty_ret = gen.fresh();
                let ty_fun = ty_fun.substitute(&env1);
                let env2 = mgu(&ty_fun, &Type::fun(ty_arg, ty_ret.clone()))?;
                let ty_ret = ty_ret.substitute(&env2);
                Ok((ty_ret, env2.substitute(&env1.substitute(&env0))))
            }
            //      Γ ⊢ e₀:t,S₀    S₀Γ,x:S₀Γ(t) ⊢ e₁:t',S₁
            // (Abs)--------------------------------------
            //          Γ ⊢ let x = e₀ in e₁:t',S₁S₀
            Exp::Let(name, arg, body) => {
                let mut ctx = ctx.clone();
                ctx.remove(name);
                let (ty_arg, env0) = arg.infer(&ctx, gen)?;
                let scheme = ty_arg.generalise(&ctx.substitute(&env0));
                ctx.insert(name.clone(), scheme);
                let (ty_body, env1) = body.infer(&ctx.substitute(&env0), gen)?;
                Ok((ty_body, env1.substitute(&env0)))
            }
            Exp::Error => Ok((Type::Error, Env::new())),
        }
    }
}
