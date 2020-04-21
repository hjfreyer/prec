use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use crate::path;
use crate::path::{Path, View as PView};
use crate::rewrite;
use func::{Func, View as FView};
use rewrite::{Rewrite, View as RView};

pub trait Metapath {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>>;
    fn unchecked_apply(&self, start: &Path) -> Path;
}

pub trait Matcher {
    type MP: Metapath;

    fn match_start(&self, start: &Endpoints<Func>) -> Option<Self::MP> {
        unimplemented!()
    }

    fn match_end(&self, end: &Endpoints<Func>) -> Option<Self::MP> {
        unimplemented!()
    }
}

#[derive(Clone, Debug)]
pub struct Reverse(Endpoints<Func>);

impl Metapath for Reverse {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(Endpoints(start, end)) = self.clone();
        Endpoints(Endpoints(start.clone(), end.clone()), Endpoints(end, start))
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        Path::validate(PView::Reverse(start.clone())).unwrap()
    }
}

pub struct ReverseMatcher();

impl Matcher for ReverseMatcher {
    type MP = Reverse;
    fn match_end(&self, Endpoints(start, end): &Endpoints<Func>) -> Option<Self::MP> {
        Some(Reverse(Endpoints(end.clone(), start.clone())))
    }
}

#[derive(Clone, Debug)]
pub struct Extend(Path, Path);

impl Metapath for Extend {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(prefix, suffix) = self.clone();
        Endpoints(
            Endpoints(
                prefix.endpoints().end().clone(),
                suffix.endpoints().start().clone(),
            ),
            Endpoints(
                prefix.endpoints().start().clone(),
                suffix.endpoints().end().clone(),
            ),
        )
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        let Self(prefix, suffix) = self.clone();
        let p1 = Path::validate(PView::Concat(prefix, start.clone())).unwrap();
        Path::validate(PView::Concat(p1, suffix)).unwrap()
    }
}

pub struct ExtendMatcher(Path, Path);

impl Matcher for ExtendMatcher {
    type MP = Extend;
    fn match_end(&self, end_path: &Endpoints<Func>) -> Option<Self::MP> {
        let Self(prefix, suffix) = self;
        if prefix.endpoints().start().syntax_eq(end_path.start())
            && end_path.end().syntax_eq(&suffix.endpoints().end())
        {
            return Some(Extend(prefix.clone(), suffix.clone()));
        }
        None
    }
}

pub struct SimplifyMatcher();

impl Matcher for SimplifyMatcher {
    type MP = Extend;
    fn match_end(&self, Endpoints(end_start, end_end): &Endpoints<Func>) -> Option<Self::MP> {
        let start_reducer = path::reduce_fully(end_start);
        let end_reducer = path::reduce_fully(end_end);

        Some(Extend(
            start_reducer,
            Path::validate(PView::Reverse(end_reducer)).unwrap(),
        ))
    }
}

pub struct Induction(pub Func, pub Func);

impl Metapath for Induction {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(f, s_case) = self;

        let func::Arity(_, f_arity) = f.arity();
        let start_start = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
        let start_end = Func::comp(
            s_case.clone(),
            Func::stack(f.clone(), Func::eye(f_arity)).unwrap(),
        )
        .unwrap();

        let end_start = f.clone();
        let end_end = Func::rec(
            Func::comp(f.clone(), Func::z_eye(f_arity)).unwrap(),
            s_case.clone(),
        )
        .unwrap();

        Endpoints(
            Endpoints(start_start, start_end),
            Endpoints(end_start, end_end),
        )
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        unimplemented!()
    }
}

pub struct RecZ(pub Func, pub Func, pub Func);

impl Metapath for RecZ {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(z_start, z_end, s_case) = self;
        Endpoints(
            Endpoints(z_start.clone(), z_end.clone()),
            Endpoints(
                Func::rec(z_start.clone(), s_case.clone()).unwrap(),
                Func::rec(z_end.clone(), s_case.clone()).unwrap(),
            ),
        )
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        unimplemented!()
    }
}

pub struct RecZMatcher();

impl Matcher for RecZMatcher {
    type MP = RecZ;
    fn match_end(&self, Endpoints(end_start, end_end): &Endpoints<Func>) -> Option<Self::MP> {
        if let (FView::Rec(start_z, start_s), FView::Rec(end_z, end_s)) =
            (end_start.view(), end_end.view())
        {
            if start_s.syntax_eq(end_s) {
                return Some(RecZ(start_z.clone(), end_z.clone(), start_s.clone()));
            }
        }
        None
    }
}

pub struct RecS(pub Func, pub Func, pub Func);

impl Metapath for RecS {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(z_case, s_start, s_end) = self;
        Endpoints(
            Endpoints(s_start.clone(), s_end.clone()),
            Endpoints(
                Func::rec(z_case.clone(), s_start.clone()).unwrap(),
                Func::rec(z_case.clone(), s_end.clone()).unwrap(),
            ),
        )
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        unimplemented!()
    }
}

pub struct RecSMatcher();

impl Matcher for RecSMatcher {
    type MP = RecS;
    fn match_end(&self, Endpoints(end_start, end_end): &Endpoints<Func>) -> Option<Self::MP> {
        if let (FView::Rec(start_z, start_s), FView::Rec(end_z, end_s)) =
            (end_start.view(), end_end.view())
        {
            if start_z.syntax_eq(end_z) {
                return Some(RecS(start_z.clone(), start_s.clone(), end_s.clone()));
            }
        }
        None
    }
}
