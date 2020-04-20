use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use crate::path;
use crate::path::{Path, View as PView};
use crate::rewrite;
use func::{Func, View as FView};
use rewrite::{Rewrite, View as RView};

pub enum View {
    RecZ(Endpoints<Func>, Func),
    RecS(Func, Endpoints<Func>),
}

pub enum ApplicationError {
    TypeMismatch(Endpoints<Func>, Path),
}

pub trait Metapath {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>>;
    fn unchecked_apply(&self, start: &Path) -> Path;
}

pub trait Matcher {
    fn match_start(&self, start: &Endpoints<Func>) -> Option<Box<dyn Metapath>> {
        unimplemented!()
    }

    fn match_end(&self, end: &Endpoints<Func>) -> Option<Box<dyn Metapath>> {
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
    fn match_end(&self, Endpoints(start, end): &Endpoints<Func>) -> Option<Box<dyn Metapath>> {
        Some(Box::new(Reverse(Endpoints(end.clone(), start.clone()))))
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
    fn match_end(&self, end_path: &Endpoints<Func>) -> Option<Box<dyn Metapath>> {
        let Self(prefix, suffix) = self;
        if prefix.endpoints().start().syntax_eq(end_path.start())
            && end_path.end().syntax_eq(&suffix.endpoints().end())
        {
            return Some(Box::new(Extend(prefix.clone(), suffix.clone())));
        }
        None
    }
}

pub struct SimplifyMatcher();

impl Matcher for SimplifyMatcher {
    fn match_end(
        &self,
        Endpoints(end_start, end_end): &Endpoints<Func>,
    ) -> Option<Box<dyn Metapath>> {
        let start_reducer = path::reduce_fully(end_start);
        let end_reducer = path::reduce_fully(end_end);

        Some(Box::new(Extend(
            start_reducer,
            Path::validate(PView::Reverse(end_reducer)).unwrap(),
        )))
    }
}


pub struct Induction(pub Func, pub Func);

impl Metapath for Induction {
    fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        let Self(f, s_case) = self;
        
        let func::Arity(_, f_arity) = f.arity();
        let start_start = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
        let start_end =
            Func::comp(s_case.clone(), Func::stack(f.clone(), Func::eye(f_arity)).unwrap()).unwrap();

        let end_start = f.clone();
        let end_end = Func::rec(Func::comp(f.clone(), Func::z_eye(f_arity)).unwrap(), s_case.clone()).unwrap();

        Endpoints(Endpoints(start_start, start_end), Endpoints(end_start, end_end))
    }

    fn unchecked_apply(&self, start: &Path) -> Path {
        Path::validate(PView::Reverse(start.clone())).unwrap()
    }
}

// pub struct InductionMatcher();

// impl Matcher for InductionMatcher {
//     fn match_end(&self, Endpoints(start, end): &Endpoints<Func>) -> Option<Box<dyn Metapath>> {
//         Some(Box::new(Reverse(Endpoints(end.clone(), start.clone()))))
//     }
// }

// #[derive(Clone, Debug)]
// pub struct ExtendEnd(Endpoints<Func>);

// impl Metapath for ExtendEnd {
//     fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
//         let Self(Endpoints(start, end)) = self.clone();
//         Endpoints(Endpoints(start.clone(), end.clone()), Endpoints(end, start))
//     }

//     fn apply(self, start: &Path) -> Result<Path, ApplicationError> {
//         let Self(ep) = self;
//         if !ep.syntax_eq(&start.endpoints()) {
//             return Err(ApplicationError::TypeMismatch(ep, start.clone()));
//         }

//         Ok(Path::validate(PView::Reverse(start.clone())).unwrap())
//     }

//     fn match_end(Endpoints(start, end): &Endpoints<Func>) -> Option<Self> {
//         Some(Self(Endpoints(end.clone(), start.clone())))
//     }
// }

// #[derive(Clone, Debug)]
// pub struct RecZ(Endpoints<Func>, Func);

// impl Metapath for RecZ {
//     fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
//         let RecZ(Endpoints(z_start, z_end), s_case) = self;
//         Endpoints(
//             Endpoints(z_start.clone(), z_end.clone()),
//             Endpoints(
//                 Func::rec(z_start.clone(), s_case.clone()).unwrap(),
//                 Func::rec(z_end.clone(), s_case.clone()).unwrap(),
//             ),
//         )
//     }

//     fn apply(self, start: &Path) -> Result<Path, ApplicationError> {
//         let RecZ(z_ep, s_case) = self;
//         if !z_ep.syntax_eq(&start.endpoints()) {
//             return Err(ApplicationError::TypeMismatch(z_ep, start.clone()));
//         }

//         Ok(Path::validate(PView::RecZ(start.clone(), s_case)).unwrap())
//     }

//     fn match_end(Endpoints(start, end): &Endpoints<Func>) -> Option<Self> {
//         if let FView::Rec(s_z_case, s_s_case) = start.view() {
//             if let FView::Rec(e_z_case, e_s_case) = end.view() {
//                 if s_s_case.syntax_eq(e_s_case) {
//                     return Some(Self(
//                         Endpoints(s_z_case.clone(), e_z_case.clone()),
//                         s_s_case.clone(),
//                     ));
//                 }
//             }
//         }
//         None
//     }
// }
