// // CompAssoc(f, g, h, i): (f ~ ((g h) i)) -> (f ~ (g (h i)))
// //   Rev: (f ~ (g (h i))) -> (f ~ ((g h) i))

use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use crate::func::{BadFunc, Func, View as FView};
use crate::path::{Path, View as PView};
use crate::rewrite;
use im::vector::Vector;
use std::fmt;
use std::mem;
use std::rc::Rc;

use crate::metapath;
use metapath::{Matcher as MetapathMatcher, Metapath};

pub enum Context {
    Empty,
    Cons(Path, Rc<Context>),
}

#[derive(Clone)]
pub enum ContextSpec {
    Empty,
    Cons(Endpoints<Func>, Rc<ContextSpec>),
}

impl ContextSpec {
    pub fn iter(&self) -> ContextSpecIntoIter {
        self.clone().into_iter()
    }

    pub fn cons(car: Endpoints<Func>, cdr: ContextSpec) -> Self {
        Self::Cons(car, Rc::new(cdr))
    }
}

impl IntoIterator for ContextSpec {
    type Item = Endpoints<Func>;
    type IntoIter = ContextSpecIntoIter;
    fn into_iter(self) -> ContextSpecIntoIter {
        ContextSpecIntoIter(self)
    }
}

pub struct ContextSpecIntoIter(ContextSpec);
impl Iterator for ContextSpecIntoIter {
    type Item = Endpoints<Func>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.0.clone() {
            ContextSpec::Empty => None,
            ContextSpec::Cons(car, cdr) => {
                self.0 = (*cdr).clone();
                Some(car)
            }
        }
    }
}

impl SyntaxEq for ContextSpec {
    fn syntax_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (ContextSpec::Empty, ContextSpec::Empty) => true,
            (ContextSpec::Empty, _) => false,
            (ContextSpec::Cons(s_car, s_cdr), ContextSpec::Cons(o_car, o_cdr)) => {
                s_car.syntax_eq(o_car) && s_cdr.syntax_eq(o_cdr)
            }
            (ContextSpec::Cons(_, _), _) => false,
        }
    }
}
impl fmt::Debug for ContextSpec {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in (0..self.iter().count() - 1) {
            fmt.write_str("  ")?
        }
        if let Some(head) = self.iter().next() {
            fmt.write_fmt(format_args!("{:?} -> {:?}", head.start(), head.end()))?;
        }
        Ok(())
    }
}

pub trait MetaMultipath {
    fn endpoints(&self) -> Endpoints<ContextSpec>;
    fn unchecked_apply(&self, start: &Context) -> Context;
}

pub trait MetaMultipathMatcher {
    type MMP: MetaMultipath;
    fn match_start(&self, start: &ContextSpec) -> Option<Self::MMP> {
        unimplemented!()
    }

    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        unimplemented!()
    }
}

pub struct PushRefl(Func, ContextSpec);

impl MetaMultipath for PushRefl {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let PushRefl(f, ctx) = self;
        Endpoints(
            ctx.clone(),
            ContextSpec::cons(Endpoints(f.clone(), f.clone()), ctx.clone()),
        )
    }

    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}

pub struct PushReflMatcher();

impl MetaMultipathMatcher for PushReflMatcher {
    type MMP = PushRefl;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        if let ContextSpec::Cons(Endpoints(start, end), cdr) = end {
            if start.syntax_eq(end) {
                return Some(PushRefl(start.clone(), (**cdr).clone()));
            }
        }
        None
    }
}

pub struct Cut(pub Func, pub Func, pub Func, pub ContextSpec);

impl MetaMultipath for Cut {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let Self(a, b, c, ctx) = self;
        Endpoints(
            ContextSpec::cons(
                Endpoints(a.clone(), b.clone()),
                ContextSpec::cons(Endpoints(b.clone(), c.clone()), ctx.clone()),
            ),
            ContextSpec::cons(Endpoints(a.clone(), c.clone()), ctx.clone()),
        )
    }

    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}

pub struct CutMatcher(pub Func);

impl MetaMultipathMatcher for CutMatcher {
    type MMP = Cut;
    fn match_end(&self, end_path: &ContextSpec) -> Option<Self::MMP> {
        let CutMatcher(mid) = self;
        if let ContextSpec::Cons(Endpoints(start, end), cdr) = end_path {
            return Some(Cut(
                start.clone(),
                mid.clone(),
                end.clone(),
                (**cdr).clone(),
            ));
        }
        None
    }
}

pub struct Concat<MMP1: MetaMultipath, MMP2: MetaMultipath>(pub MMP1, pub MMP2);

impl<MMP1: MetaMultipath, MMP2: MetaMultipath> MetaMultipath for Concat<MMP1, MMP2> {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let Self(p1, p2) = self;
        Endpoints(p1.endpoints().start().clone(), p2.endpoints().end().clone())
    }

    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}
pub struct ConcatMatcher<MMPM1: MetaMultipathMatcher, MMPM2: MetaMultipathMatcher>(
    pub MMPM1,
    pub MMPM2,
);

impl<MMPM1: MetaMultipathMatcher, MMPM2: MetaMultipathMatcher> MetaMultipathMatcher
    for ConcatMatcher<MMPM1, MMPM2>
{
    type MMP = Concat<MMPM1::MMP, MMPM2::MMP>;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        let ConcatMatcher(m1, m2) = self;
        if let Some(p2) = m2.match_end(end) {
            let mid = p2.endpoints().start().clone();
            if let Some(p1) = m1.match_end(&mid) {
                return Some(Concat(p1, p2));
            }
        }
        None
    }
}

pub struct Lift<MP: Metapath>(MP, ContextSpec);

impl<MP: Metapath> MetaMultipath for Lift<MP> {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let Self(mp, ctx) = self;
        let Endpoints(start, end) = mp.endpoints();
        Endpoints(
            ContextSpec::cons(start, ctx.clone()),
            ContextSpec::cons(end, ctx.clone()),
        )
    }
    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}
pub struct LiftMatcher<MPM: MetapathMatcher>(pub MPM);

impl<MPM: MetapathMatcher> MetaMultipathMatcher for LiftMatcher<MPM> {
    type MMP = Lift<MPM::MP>;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        let LiftMatcher(lift_matcher) = self;
        if let ContextSpec::Cons(ep, cdr) = end {
            if let Some(m) = lift_matcher.match_end(ep) {
                return Some(Lift(m, (**cdr).clone()));
            }
        }
        None
    }
}

pub struct Lift2<MP: Metapath>(Endpoints<Func>, MP, ContextSpec);

impl<MP: Metapath> MetaMultipath for Lift2<MP> {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let Self(head, mp, ctx) = self;
        let Endpoints(start, end) = mp.endpoints();
        Endpoints(
            ContextSpec::cons(head.clone(), ContextSpec::cons(start, ctx.clone())),
            ContextSpec::cons(head.clone(), ContextSpec::cons(end, ctx.clone())),
        )
    }
    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}
pub struct Lift2Matcher<MPM: MetapathMatcher + ?Sized>(pub MPM);

impl<MPM: MetapathMatcher + ?Sized> MetaMultipathMatcher for Lift2Matcher<MPM> {
    type MMP = Lift2<MPM::MP>;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        let Self(lift_matcher) = self;
        if let ContextSpec::Cons(head, cdr) = end {
            if let ContextSpec::Cons(ep, cdr) = &**cdr {
                if let Some(m) = lift_matcher.match_end(ep) {
                    return Some(Lift2(head.clone(), m, (**cdr).clone()));
                }
            }
        }
        None
    }
}

pub struct Induction(metapath::Induction, Func, ContextSpec);

impl MetaMultipath for Induction {
    fn endpoints(&self) -> Endpoints<ContextSpec> {
        let Self(ind, target, ctx) = self;
        let Endpoints(Endpoints(f_s, s_applied), Endpoints(f, rec)) = ind.endpoints();
        Endpoints(
            ContextSpec::cons(
                Endpoints(f_s.clone(), s_applied.clone()),
                ContextSpec::cons(Endpoints(rec.clone(), target.clone()), ctx.clone()),
            ),
            ContextSpec::cons(Endpoints(f.clone(), target.clone()), ctx.clone()),
        )
    }
    fn unchecked_apply(&self, start: &Context) -> Context {
        unimplemented!()
    }
}
pub struct InductionMatcher(pub Func);

impl MetaMultipathMatcher for InductionMatcher {
    type MMP = Induction;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        let InductionMatcher(s_case) = self;
        if let ContextSpec::Cons(Endpoints(f, target), cdr) = end {
            return Some(Induction(
                metapath::Induction(f.clone(), s_case.clone()),
                target.clone(),
                (**cdr).clone(),
            ));
        }
        None
    }
}

pub struct RecCutMatcher();

impl MetaMultipathMatcher for RecCutMatcher {
    type MMP = Cut;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        if let ContextSpec::Cons(Endpoints(start_rec, end_rec), cdr) = end {
            if let (FView::Rec(start_z, start_s), FView::Rec(end_z, end_s)) =
                (start_rec.view(), end_rec.view())
            {
                let midpoint = Func::rec(end_z.clone(), start_s.clone()).unwrap();
                return CutMatcher(midpoint).match_end(end);
            }
        }
        None
    }
}

pub struct RecSplitMatcher();

impl MetaMultipathMatcher for RecSplitMatcher {
    type MMP = Concat<Lift<metapath::RecZ>, Concat<Lift2<metapath::RecS>, Cut>>;
    fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
        ConcatMatcher(
            LiftMatcher(metapath::RecZMatcher()),
            ConcatMatcher(Lift2Matcher(metapath::RecSMatcher()), RecCutMatcher()),
        )
        .match_end(end)
    }
}
