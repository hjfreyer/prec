use crate::base::{Endpoints, SyntaxEq, Transform, TypedPoint};
use crate::func;
use crate::pattern;
use crate::rewrite;
use crate::rewrite::Rewrite;
use func::View as FView;
use func::{BadFunc, Func};
use im::Vector;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Action(View);

#[derive(Clone, Debug)]
pub enum View {
    Reverse,

    Extend(Rewrite),

    // Induction.
    Induction,

    // Upgrade a path to one inside a nested structure.
    CompLeft(Func),
    CompRight(Func),
    StackCar(Func),
    StackCdr(Func),
    RecZ(Func),
    RecS(Func),
}

pub trait Tactic {
    fn apply(&self, ep: &Endpoints<Func>) -> Option<(Endpoints<Func>, Vector<Action>)>;
}

pub fn induction() -> impl Tactic {
    struct Impl();
    impl Tactic for Impl {
        fn apply(
            &self,
            Endpoints(f, rec): &Endpoints<Func>,
        ) -> Option<(Endpoints<Func>, Vector<Action>)> {
            let f_arity = f.arity().r#in();
            let (z_case, s_case) = rec.unrec()?;
            let (z_f, z_g) = z_case.decompose()?;
            if !z_f.syntax_eq(f) || !z_g.syntax_eq(&Func::z_eye(f_arity)) {
                return None;
            }

            let start_start = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
            let start_end = Func::comp(
                s_case.clone(),
                Func::stack(f.clone(), Func::eye(f_arity)).unwrap(),
            )
            .unwrap();

            Some((
                Endpoints(start_start, start_end),
                im::vector![Action(View::Induction)],
            ))
        }
    }
    Impl()
}

// pub fn extend<T : rewrite::Tactic>(t : T) -> impl Tactic {
//     struct Impl<T : rewrite::Tactic>(T);
//     impl <T : rewrite::Tactic> Tactic for Impl<T> {
//         fn apply(&self, end_path: &Endpoints<Func>) -> Option<(Endpoints<Func>, Vector<Action>)> {
//             let Self(rw_tactic) = self;
//             let (rewritten, rewrites) = rw_tactic.apply(end_path.end())?;
//             let wrapped_rewrites = rewrites.into_iter().map(|rw| Action(View::Extend(rw))).collect();
//             Some((Endpoints(end_path.start().clone(), rewritten), wrapped_rewrites))
//         }
//     }
//     Impl(t)
// }

impl<RW: rewrite::Tactic> Tactic for RW {
    fn apply(&self, end_path: &Endpoints<Func>) -> Option<(Endpoints<Func>, Vector<Action>)> {
        let (rewritten, rewrites) = self.apply(end_path.end())?;
        let wrapped_rewrites = rewrites
            .into_iter()
            .map(|rw| Action(View::Extend(rw)))
            .collect();
        Some((
            Endpoints(end_path.start().clone(), rewritten),
            wrapped_rewrites,
        ))
    }
}

pub fn reverse() -> impl Tactic {
    struct Impl();
    impl Tactic for Impl {
        fn apply(
            &self,
            Endpoints(start, end): &Endpoints<Func>,
        ) -> Option<(Endpoints<Func>, Vector<Action>)> {
            Some((
                Endpoints(end.clone(), start.clone()),
                im::vector![Action(View::Reverse)],
            ))
        }
    }
    Impl()
}

pub fn rec_z() -> impl Tactic {
    struct Impl();
    impl Tactic for Impl {
        fn apply(
            &self,
            Endpoints(start, end): &Endpoints<Func>,
        ) -> Option<(Endpoints<Func>, Vector<Action>)> {
            let (start_z, start_s) = start.unrec()?;
            let (end_z, end_s) = end.unrec()?;
            if start_s.syntax_eq(&end_s) {
                Some((
                    Endpoints(start_z, end_z),
                    im::vector![Action(View::RecZ(start_s))],
                ))
            } else {
                None
            }
        }
    }
    Impl()
}

// #[derive(Clone, Debug)]
// pub enum BadPath {
//     IncompatibleArity(Func, Func),
// }

// impl Action {
//     pub fn validate(view: View) -> Result<Action, BadPath> {
//         // TODO: Validate.
//         Ok(Self(Rc::new(view)))
//     }

//     pub fn endpoints(&self) -> Endpoints<Func> {
//         match &*self.0 {
//             // View::Refl(f) => Endpoints(f.clone(), f.clone()),
//             View::Reverse(Endpoints(start, end)) => {
//                 Endpoints(end, start)
//             }
//             // View::Concat(left, right) => Endpoints(
//             //     left.endpoints().start().clone(),
//             //     right.endpoints().end().clone(),
//             // ),

//             View::Rewrite(path, rw) => Endpoints(path.start().clone(), rw.endpoints().end().clone()),

//             View::Induction(f, s_case, _) => Endpoints(
//                 f.clone(),
//                 Func::rec(
//                     Func::comp(f.clone(), Func::z_eye(f.arity().r#in())).unwrap(),
//                     s_case.clone(),
//                 )
//                 .unwrap(),
//             ),

//             View::CompLeft(f_rw, g) => Endpoints(
//                 Func::comp(f_rw.start().clone(), g.clone()).unwrap(),
//                 Func::comp(f_rw.end().clone(), g.clone()).unwrap(),
//             ),
//             View::CompRight(f, g_rw) => Endpoints(
//                 Func::comp(f.clone(), g_rw.start().clone()).unwrap(),
//                 Func::comp(f.clone(), g_rw.end().clone()).unwrap(),
//             ),
//             View::StackCar(car_rw, cdr) => Endpoints(
//                 Func::stack(car_rw.start().clone(), cdr.clone()).unwrap(),
//                 Func::stack(car_rw.end().clone(), cdr.clone()).unwrap(),
//             ),
//             View::StackCdr(car, cdr_rw) => Endpoints(
//                 Func::stack(car.clone(), cdr_rw.start().clone()).unwrap(),
//                 Func::stack(car.clone(), cdr_rw.end().clone()).unwrap(),
//             ),
//             View::RecZ(z_rw, s_case) => Endpoints(
//                 Func::rec(z_rw.start().clone(), s_case.clone()).unwrap(),
//                 Func::rec(z_rw.end().clone(), s_case.clone()).unwrap(),
//             ),
//             View::RecS(z_case, s_rw) => Endpoints(
//                 Func::rec(z_case.clone(), s_rw.start().clone()).unwrap(),
//                 Func::rec(z_case.clone(), s_rw.end().clone()).unwrap(),
//             ),
//         }
//     }
// }

// // impl TypedPoint for Func {
// //     type Type = Func;
// //     type
// // }

// // pub trait PathFinder {
// //     fn match_start(&self, func: &Func) -> Option<Path>;
// // }

// // pub fn refl() -> impl PathFinder {
// //     impl PathFinder for () {
// //         fn match_start(&self, func: &Func) -> Option<Path> {
// //             Some(Path::validate(View::Refl(func.clone())).unwrap())
// //         }
// //     }
// // }

// // pub struct Reducer();

// // impl PathFinder for Reducer {
// //     fn match_start(&self, func: &Func) -> Option<Path> {
// //         Some(reduce_fully(func))
// //     }
// // }

// // fn factor() -> impl PathFinder {
// //     struct Impl();

// // impl PathFinder for Impl {
// //     fn match_start(&self, func: &Func) -> Option<Path> {
// //         rewrite::comp_factor_stack()(func)
// //         let Self(factored) = self;
// //         let proposal = Path::validate(View::Reverse(Rewrite::validate(RView::CompDistributeEmpty(factored)).unwrap())).unwrap();
// //         if proposal.endpoints().start().syntax_eq(func) {
// //             Some(proposal)
// //         } else {
// //             None
// //         }
// //     }
// // }
// // Impl()
// // }
