use crate::{
    Binder1,
    BinderN,
    Comp,
    Ident,
    Pattern,
    Val,
};

use std::collections::HashMap;

fn try_vec_1<T>(mut v: Vec<T>) -> Result<T, Vec<T>> {
    if v.len() == 1 {
        Ok(v.pop().unwrap())
    } else {
        Err(v)
    }
}

impl Binder1 {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>) -> Self { match self {
        Binder1::Eq(b, vs1, vs2) => {
            let vs1 = vs1.into_iter()
                .map(|v| v.unroll_rec(defs)).collect();
            let vs2 = vs2.into_iter()
                .map(|v| v.unroll_rec(defs)).collect();
            Binder1::Eq(b, vs1, vs2)
        }
        Binder1::LogQuantifier(q, xs, m) => {
            let m = Box::new(m.unroll_rec(defs));
            Binder1::LogQuantifier(q, xs, m)
        }
        Binder1::LogOp1(o, v) => {
            let v = v.unroll_rec(defs);
            Binder1::LogOp1(o, v)
        }
        Binder1::LogOpN(o, vs) => {
            let vs = vs.into_iter().map(|v| v.unroll_rec(defs)).collect();
            Binder1::LogOpN(o, vs)
        }
        Binder1::QMode(q, m) => Binder1::QMode(q, Box::new(m.unroll_rec(defs))),
    }}
}

impl BinderN {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>) -> Self { match self {
        BinderN::Call(c) => BinderN::Call(c),
        BinderN::Seq(m) => BinderN::Seq(Box::new(m.unroll_rec(defs))),
    }}
}

impl Comp {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>) -> Self { match self {
        Self::Apply(m, ts, vs) => Self::Apply(Box::new(m.unroll_rec(defs)), ts, vs),
        Self::Bind1(b, x, m) => Self::Bind1(b.unroll_rec(defs), x, Box::new(m.unroll_rec(defs))),
        Self::BindN(b, ps, m2) => match try_vec_1(ps) {
            // For a "let _ = ..", we don't actually want to unroll
            // the right side of the let, since this is being used as
            // an instantiation.
            Ok(Pattern::NoBind) => Self::BindN(b, vec![Pattern::NoBind], Box::new(m2.unroll_rec(defs))),
            Ok(p) => Self::BindN(b.unroll_rec(defs), vec![p], Box::new(m2.unroll_rec(defs))),
            Err(ps) => Self::BindN(b.unroll_rec(defs), ps, Box::new(m2.unroll_rec(defs))),
        }
        Self::Force(v) => Self::Force(v.unroll_rec(defs)),
        Self::Fun(xs, m) => {
            let m = Box::new(m.unroll_rec(defs));
            Self::Fun(xs, m)
        }
        Self::Ite(v, m1, m2) => {
            let v = v.unroll_rec(defs);
            let m1 = Box::new(m1.unroll_rec(defs));
            let m2 = Box::new(m2.unroll_rec(defs));
            Self::Ite(v, m1, m2)
        }
        Self::Match(v, arms) => {
            let v = v.unroll_rec(defs);
            let arms = arms.into_iter()
                .map(|(a, m)| (a, Box::new(m.unroll_rec(defs))))
                .collect();
            Self::Match(v, arms)
        }
        Self::Return(vs) => Self::Return(vs.into_iter().map(|v| v.unroll_rec(defs)).collect()),
    }}
}

impl Val {
    pub fn unroll_rec(self, defs: &HashMap<String, Comp>) -> Self { match self {
        Val::Thunk(m) => Val::Thunk(Box::new(m.unroll_rec(defs))),
        Val::Tuple(vs) => Val::Tuple(vs.into_iter().map(|v| v.unroll_rec(defs)).collect()),
        Val::Var(Ident::Manual(x), ts, path, true) => {
            match defs.get(&x) {
                Some(def) => {
                    Val::Thunk(Box::new(def.clone().builder().flatten().build_no_context()))
                }
                None => Val::Var(Ident::Manual(x), ts, path, true),
            }
        }
        v => v,
    }}
}
