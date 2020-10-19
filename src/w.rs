// Derived from https://github.com/nwoeanhinnogaehr/algorithmw-rust
use crate::ast::result::{Result, TypeError};
use crate::ast::*;
use std::fmt::Debug;

impl<T: Debug + Clone> Env<T> {
    /// Construct an empty environment.
    pub fn new() -> Self {
        Self(Map::new())
    }
    /// Union `self` with `other` and prefer elements of `self` in the case of intersection.
    pub fn union(self, other: Self) -> Self {
        Self(self.0.into_iter().chain(other.0).collect())
    }
    /// Intersect `self` with `other` and prefer elements of `self` in the case of intersection.
    pub fn intersection(self, other: Self) -> Self {
        Self(
            self.0
                .into_iter()
                .filter(|(name, _)| other.0.contains_key(name))
                .collect(),
        )
    }
}

pub trait TypeMethods {
    /// Returns the set of free type variables of self
    fn ftv(&self) -> Set<Name>;
    /// Applies a substitution to self
    fn substitute(&self, env: &Env<Type>) -> Self;
}

impl Type {
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
                        .try_fold(Env::new(), |env0, (param1, param2)| {
                            let param1 = param1.substitute(&env0);
                            let param2 = param2.substitute(&env0);
                            let env1 = Type::mgu(&param1, &param2)?;
                            Ok(env1.substitute(&env0))
                        })
                }
            }
            (Type::Error, _) | (_, Type::Error) => Ok(Env::new()),
        }
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
    pub fn specialise(&self, gen: &mut Gen) -> Type {
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
    pub fn generalise(self: &Type, ctx: &Env<Scheme>) -> Scheme {
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
        let (t, s) = self.infer(ctx, &mut gen)?;
        Ok(t.substitute(&s))
    }

    fn infer(&self, ctx: &Env<Scheme>, gen: &mut Gen) -> Result<(Type, Env<Type>)> {
        match self {
            Exp::Lit(l) => match l {
                Lit::Int(_) => Ok((Type::int(), Env::new())),
                Lit::Bool(_) => Ok((Type::bool(), Env::new())),
                Lit::Str(_) => Ok((Type::str(), Env::new())),
            },
            //      x:p ∈ Γ   t = specialise(p)
            // (Var)---------------------------
            //            Γ ⊢ x:t,∅
            Exp::Var(x) => ctx
                .get(x)
                .map(|p| (p.specialise(gen), Env::new()))
                .ok_or_else(|| {
                    TypeError(format!("Term is not closed, found free variable: {}", x))
                }),
            //      t₀ = fresh()   Γ,x:t₀ ⊢ e:t₁,S₀
            // (Abs)-------------------------------
            //          Γ ⊢ λx.e:S₀t₀ → t₁,S₀
            Exp::Abs(x, e) => {
                let t0 = gen.fresh();
                let mut ctxm = ctx.clone();
                ctxm.insert(x.clone(), Scheme::Mono(t0.clone()));
                let (t1, s0) = e.infer(&ctxm, gen)?;
                Ok((Type::fun(t0.substitute(&s0), t1), s0))
            }
            //      Γ ⊢ e₀:t₀,S₀   S₀Γ ⊢ e₁:t₁,S₁   t₂ = fresh()   S₂ = mgu(S₁t₀, t₁ → t₂)
            // (App)----------------------------------------------------------------------
            //                         Γ ⊢ e₀ e₁:S₂t₂,S₂S₁S₀
            Exp::App(e0, e1) => {
                let (t0, s0) = e0.infer(ctx, gen)?;
                let (t1, s1) = e1.infer(&ctx.substitute(&s0), gen)?;
                let t2 = gen.fresh();
                let s2 = Type::mgu(&t0.substitute(&s1), &Type::fun(t1, t2.clone()))?;
                Ok((t2.substitute(&s2), s2.substitute(&s1.substitute(&s0))))
            }
            //      Γ ⊢ e₀:t₀,S₀   a = fv(t) - fv(S₀Γ)   S₀Γ,x:∀a.t₀ ⊢ e₁:t₁,S₁
            // (Let)-----------------------------------------------------------
            //               Γ ⊢ let x = e₀ in e₁:t₁,S₁S₀
            Exp::Let(x, e0, e1) => {
                let (t0, s0) = e0.infer(&ctx, gen)?;
                let mut ctxp = ctx.clone();
                ctxp.remove(x);
                let p = t0.generalise(&ctxp.substitute(&s0));
                ctxp.insert(x.clone(), p);
                let (t1, s1) = e1.infer(&ctxp.substitute(&s0), gen)?;
                Ok((t1, s1.substitute(&s0)))
            }
            //         Γ,x:t₀ ⊢ e₀:t₀,S₀   a = fv(t) - fv(S₀Γ)   S₀Γ,x:∀a.t₀ ⊢ e₁:t₁,S₁
            // (LetRec)----------------------------------------------------------------
            //               Γ ⊢ let rec x = e₀ in e₁:t₁
            Exp::LetRec(x, e0, e1) => {
                let t0 = gen.fresh();
                let m = Scheme::Mono(t0.clone());
                let mut ctxm = ctx.clone();
                ctxm.insert(x.clone(), m);
                let (t0, s0) = e0.infer(&ctxm, gen)?;
                let mut ctxp = ctx.clone();
                let p = t0.generalise(&ctxp.substitute(&s0));
                ctxp.insert(x.clone(), p);
                let (t1, s1) = e1.infer(&ctxp.substitute(&s0), gen)?;
                Ok((t1, s1.substitute(&s0)))
            }
            Exp::Error => Ok((Type::Error, Env::new())),
        }
    }
}
