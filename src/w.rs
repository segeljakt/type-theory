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
    fn substitute(&self, s: &Env<Type>) -> Self;
}

impl Type {
    /// Computes the most general unifier of two types `ty1` and `ty2`
    fn mgu(t0: &Type, t1: &Type) -> Result<Env<Type>> {
        match (t0, t1) {
            (Type::Var(x), t) | (t, Type::Var(x)) => {
                if t.ftv().contains(x) {
                    Err(TypeError(format!("`{}` and `{}` are recursive", t0, t1)))
                } else {
                    let mut s = Env::new();
                    s.insert(x.clone(), t.clone());
                    Ok(s)
                }
            }
            (Type::Cons(x0, ts0), Type::Cons(x1, ts1)) => {
                if x0 != x1 || ts0.len() != ts1.len() {
                    Err(TypeError(format!("Cannot unify `{}` with `{}`", t0, t1)))
                } else {
                    ts0.iter().zip(ts1).try_fold(Env::new(), |s0, (t0, t1)| {
                        let t0 = t0.substitute(&s0);
                        let t1 = t1.substitute(&s0);
                        let s1 = Type::mgu(&t0, &t1)?;
                        Ok(s1.substitute(&s0))
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
        let t = Type::Var(format!("'t{}", self.0).into());
        self.0 += 1;
        t
    }
}

impl TypeMethods for Type {
    // Return the set of all (free) Type::Var in self
    fn ftv(&self) -> Set<Name> {
        match self {
            Type::Var(x) => {
                let mut s = Set::new();
                s.insert(x.clone());
                s
            }
            Type::Cons(_, ts) => ts.ftv(),
            Type::Error => Set::new(),
        }
    }

    // Substitute all type variables in `self` with `env`
    fn substitute(&self, s: &Env<Type>) -> Type {
        match self {
            Type::Var(x) => s.get(x).cloned().unwrap_or(self.clone()),
            Type::Cons(x, ts) => Type::Cons(x.clone(), ts.substitute(s)),
            Type::Error => Type::Error,
        }
    }
}

/// Helper methods for Type and Scheme
impl<'a, T: TypeMethods> TypeMethods for Vec<T> {
    fn ftv(&self) -> Set<Name> {
        self.iter()
            .fold(Set::new(), |ftv, t| ftv.union(&t.ftv()).cloned().collect())
    }

    fn substitute(&self, s: &Env<Type>) -> Vec<T> {
        self.iter().map(|t| t.substitute(s)).collect()
    }
}

impl TypeMethods for Scheme {
    /// The free type variables in a scheme are those that are free
    /// in the internal type and not bound by the variable mapping.
    fn ftv(&self) -> Set<Name> {
        match self {
            Scheme::Mono(t) => t.ftv(),
            Scheme::Poly(t, qs) => t.ftv().difference(&qs).cloned().collect(),
        }
    }

    /// Substitutions are applied to free type variables only.
    fn substitute(&self, s: &Env<Type>) -> Scheme {
        match self {
            Scheme::Mono(t) => Scheme::Mono(t.substitute(s)),
            Scheme::Poly(t, qs) => Scheme::Poly(
                t.substitute(&qs.iter().fold(s.clone(), |mut s, q| {
                    s.remove(q);
                    s
                })),
                qs.clone(),
            ),
        }
    }
}

impl TypeMethods for Env<Type> {
    fn ftv(&self) -> Set<Name> {
        self.values().cloned().collect::<Vec<Type>>().ftv()
    }
    fn substitute(&self, s: &Env<Type>) -> Self {
        self.clone().union(Env(s
            .iter()
            .map(|(x, t)| (x.clone(), t.substitute(self)))
            .collect()))
    }
}

impl TypeMethods for Env<Scheme> {
    /// The free type variables of a context is the union
    /// of the free type variables of each scheme in the context.
    fn ftv(&self) -> Set<Name> {
        self.values().cloned().collect::<Vec<Scheme>>().ftv()
    }

    /// To apply a substitution, we just apply it to each scheme in the type environment.
    fn substitute(&self, s: &Env<Type>) -> Env<Scheme> {
        Env(self
            .iter()
            .map(|(name, scheme)| (name.clone(), scheme.substitute(s)))
            .collect())
    }
}

impl Scheme {
    /// Specialises a scheme into a type by replacing all quantifiers
    /// with fresh type variables.
    pub fn specialise(&self, gen: &mut Gen) -> Type {
        match self {
            Scheme::Mono(t) => t.clone(),
            Scheme::Poly(t, qs) => t.substitute(&Env(qs
                .iter()
                .cloned()
                .zip(qs.iter().map(|_| gen.fresh()))
                .collect())),
        }
    }
}

impl Type {
    /// Generalises a type into a scheme by quantifying over
    /// all free variables in the type.
    pub fn generalise(&self, ctx: &Env<Scheme>) -> Scheme {
        let qs = self
            .ftv()
            .difference(&ctx.ftv())
            .cloned()
            .collect::<Set<Name>>();
        if qs.is_empty() {
            Scheme::Mono(self.clone())
        } else {
            Scheme::Poly(self.clone(), qs)
        }
    }
}

impl Exp {
    /// Perform type inference on an expression and return the resulting type, if any.
    pub fn infer_w(&self, ctx: &Env<Scheme>) -> Result<Type> {
        let mut gen = Gen::new();
        let (t, s) = self.w(ctx, &mut gen)?;
        Ok(t.substitute(&s))
    }

    /// Algorithm W
    fn w(&self, ctx: &Env<Scheme>, gen: &mut Gen) -> Result<(Type, Env<Type>)> {
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
                let (t1, s0) = e.w(&ctxm, gen)?;
                Ok((Type::fun(t0.substitute(&s0), t1), s0))
            }
            //      Γ ⊢ e₀:t₀,S₀   S₀Γ ⊢ e₁:t₁,S₁   t₂ = fresh()   S₂ = mgu(S₁t₀, t₁ → t₂)
            // (App)----------------------------------------------------------------------
            //                         Γ ⊢ e₀ e₁:S₂t₂,S₂S₁S₀
            Exp::App(e0, e1) => {
                let (t0, s0) = e0.w(ctx, gen)?;
                let (t1, s1) = e1.w(&ctx.substitute(&s0), gen)?;
                let t2 = gen.fresh();
                let s2 = Type::mgu(&t0.substitute(&s1), &Type::fun(t1, t2.clone()))?;
                Ok((t2.substitute(&s2), s2.substitute(&s1.substitute(&s0))))
            }
            //      Γ ⊢ e₀:t₀,S₀   S₀Γ ⊢ p = generalise(t₀)   S₀Γ,x:p ⊢ e₁:t₁,S₁
            // (Let)------------------------------------------------------------
            //               Γ ⊢ let x = e₀ in e₁:t₁,S₁S₀
            Exp::Let(x, e0, e1) => {
                let (t0, s0) = e0.w(&ctx, gen)?;
                let mut ctxp = ctx.clone();
                ctxp.remove(x);
                let p = t0.generalise(&ctxp.substitute(&s0));
                ctxp.insert(x.clone(), p);
                let (t1, s1) = e1.w(&ctxp.substitute(&s0), gen)?;
                Ok((t1, s1.substitute(&s0)))
            }
            //         Γ,x:t₀ ⊢ e₀:t₀,S₀   S₀Γ ⊢ p = generalise(t₀)   S₀Γ,x:p ⊢ e₁:t₁,S₁
            // (LetRec)-----------------------------------------------------------------
            //               Γ ⊢ let rec x = e₀ in e₁:t₁,S₁S₀
            Exp::LetRec(x, e0, e1) => {
                let t0 = gen.fresh();
                let m = Scheme::Mono(t0.clone());
                let mut ctxm = ctx.clone();
                ctxm.insert(x.clone(), m);
                let (t0, s0) = e0.w(&ctxm, gen)?;
                let mut ctxp = ctx.clone();
                let p = t0.generalise(&ctxp.substitute(&s0));
                ctxp.insert(x.clone(), p);
                let (t1, s1) = e1.w(&ctxp.substitute(&s0), gen)?;
                Ok((t1, s1.substitute(&s0)))
            }
            Exp::Error => Ok((Type::Error, Env::new())),
        }
    }
}
