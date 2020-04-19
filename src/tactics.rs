// CompAssoc(f, g, h, i): (f ~ ((g h) i)) -> (f ~ (g (h i)))
//   Rev: (f ~ (g (h i))) -> (f ~ ((g h) i))

use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use crate::func::{BadFunc, Func, View as FView};
use crate::rewrite;
use crate::rewrite::{Path, PathView as PView};
use im::vector::Vector;
use std::fmt;
use std::rc::Rc;

pub type Context = Vector<Path>;
pub type ContextSpec = Vector<Endpoints<Func>>;

pub struct ContextSpecWrapper(pub ContextSpec);

fn cons<T: Clone>(car: T, mut cdr: Vector<T>) -> Vector<T> {
    cdr.push_front(car);
    cdr
}

#[derive(Debug, Clone)]
pub enum Op {
    PushRefl(Func),
    Symm,
    ExtendPath(Path),
    Concat(Func),
    Induction(Func, Func),
    RecSplit(Func, Func, Func, Func), //    Induction(Func, Func, Func, )
}

impl Op {
    //   pub  fn lhs(self)-> Context {}
    //     pub fn rhs(self)-> Context {}

    pub fn forward(self, mut ctx: Context) -> Option<Context> {
        match self {
            Op::PushRefl(f) => Some(cons(Path::validate(PView::Refl(f)), ctx)),
            Op::Symm => {
                if let Some(p) = ctx.pop_front() {
                    return Some(cons(Path::validate(PView::Inverse(Box::new(p))), ctx));
                }
                None
            }
            Op::ExtendPath(p) => {
                if let Some(head_path) = ctx.pop_front() {
                    let new_head = Path::validate(PView::Concat(Box::new(head_path), Box::new(p)));
                    return Some(cons(new_head, ctx));
                }
                None
            }
            Op::Concat(mid) => {
                if let Some(car) = ctx.pop_front() {
                    if let Some(car_cdr) = ctx.pop_front() {
                        if car.endpoints().end().syntax_eq(&mid)
                            && car_cdr.endpoints().start().syntax_eq(&mid)
                        {
                            return Some(cons(
                                Path::validate(PView::Concat(Box::new(car), Box::new(car_cdr))),
                                ctx,
                            ));
                        }
                    }
                }
                None
            }
            Op::Induction(f, s_case) => {
                if let Some(car) = ctx.pop_front() {
                    if let Ok(rw) = rewrite::Rewrite::validate(
                        rewrite::View::Induction(f, s_case, Box::new(car)),
                        crate::func::Tag::None,
                    ) {
                        Some(cons(Path::validate(PView::Rewrite(rw)), ctx));
                    }
                }
                None
            }
            Op::RecSplit(l_z_case, l_s_case, r_z_case, r_s_case) => {
                if let Some(z_path) = ctx.pop_front() {
                    if let Some(s_path) = ctx.pop_front() {
                        if let Ok(replace_z_path) = rewrite::Rewrite::validate(
                            rewrite::View::RecZ(Box::new(z_path), l_s_case),
                            crate::func::Tag::None,
                        ) {
                            if let Ok(replace_s_path) = rewrite::Rewrite::validate(
                                rewrite::View::RecS(r_z_case, Box::new(s_path)),
                                crate::func::Tag::None,
                            ) {}
                        }
                    }
                }
                None
            }
        }
    }
    pub fn reverse(self, mut ctx: ContextSpec) -> Option<ContextSpec> {
        match self {
            Op::PushRefl(f) => {
                // Pop refl.
                if let Some(Endpoints(start, end)) = ctx.pop_front() {
                    if start.syntax_eq(&f) && end.syntax_eq(&f) {
                        return Some(ctx);
                    }
                }
                None
            }
            Op::Symm => {
                if let Some(Endpoints(start, end)) = ctx.pop_front() {
                    return Some(cons(Endpoints(end, start), ctx));
                }
                None
            }
            Op::ExtendPath(p) => {
                // Retract path.
                if let Some(Endpoints(start, end)) = ctx.pop_front() {
                    if end.syntax_eq(p.endpoints().end()) {
                        return Some(cons(Endpoints(start, p.endpoints().start().clone()), ctx));
                    }
                }
                None
            }
            Op::Concat(mid) => {
                // Split.
                if let Some(Endpoints(start, end)) = ctx.pop_front() {
                    return Some(cons(
                        Endpoints(start, mid.clone()),
                        cons(Endpoints(mid, end), ctx),
                    ));
                }
                None
            }
            Op::Induction(f, s_case) => {
                if let Some(Endpoints(start, end)) = ctx.pop_front() {
                    if let FView::Rec(z_case, s_case) = end.view() {
                        let func::Arity(_, f_arity) = f.arity();
                        let needed_lhs = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
                        let needed_rhs = Func::comp(
                            s_case.clone(),
                            Func::stack(f.clone(), Func::eye(f_arity)).unwrap(),
                        )
                        .unwrap();
                        return Some(cons(Endpoints(needed_lhs, needed_rhs), ctx));
                    }
                }
                None
            }
        }
    }
}

#[derive(Clone, Debug)]
pub enum Tactic {
    Ident,
    Symm,
    ReduceRight,

    Cut(Func),
    Induction(Func),
}

impl Tactic {
    pub fn for_goal(self, ctx: &ContextSpec) -> Vec<Op> {
        match self {
            Tactic::Ident => {
                if let Some(Endpoints(start, end)) = ctx.front() {
                    if start.syntax_eq(&end) {
                        return vec![Op::PushRefl(start.clone())];
                    }
                }
                vec![]
            }
            Tactic::Symm => vec![Op::Symm],
            Tactic::Cut(mid) => vec![Op::Concat(mid)],
            Tactic::Induction(s_case) => {
                if let Some(Endpoints(start, end)) = ctx.front() {
                    let z_case =
                        Func::comp(start.clone(), Func::z_eye(start.arity().r#in())).unwrap();
                    let rec_fun = Func::rec(z_case, s_case.clone()).unwrap();

                    return vec![
                        Op::Concat(rec_fun),
                        Op::Induction(start.clone(), s_case.clone()),
                    ];
                }
                vec![]
            }
            Tactic::ReduceRight => {
                if let Some(Endpoints(left, right)) = ctx.front() {
                    let path_to_reduced = rewrite::reduce_fully(right.clone());
                    let reduced = path_to_reduced.endpoints().end().clone();
                    return vec![Op::ExtendPath(Path::validate(PView::Inverse(Box::new(
                        path_to_reduced,
                    ))))];
                }
                vec![]
            }
        }
    }
}

impl fmt::Debug for ContextSpecWrapper {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        let ContextSpecWrapper(s) = self;
        for _ in 0..(s.len() - 1) {
            fmt.write_str("  ")?
        }
        if s.len() > 0 {
            fmt.write_fmt(format_args!("{:?} -> {:?}", s[0].start(), s[0].end()))?;
        }
        Ok(())
        //     match g {
        //         Goal::Active(s, e) => {
        //             for _ in 0..indent {
        //                 fmt.write_str("  ")?
        //             }
        //             fmt.write_fmt(format_args!("{:?} -> {:?} ACTIVE\n", s, e))?;
        //             Ok(true)
        //         }
        //         Goal::Resolved(p) => {
        //             for _ in 0..indent {
        //                 fmt.write_str("  ")?
        //             }
        //             fmt.write_fmt(format_args!("{:?} -> {:?} DONE\n", p.start(), p.end()))?;
        //             Ok(false)
        //         }
        //         g @ Goal::Unary(name, box sub, _, _) => {
        //             for _ in 0..indent {
        //                 fmt.write_str("  ")?
        //             }
        //             let Endpoints(start, end) = g.overall_goal();
        //             fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, name))?;
        //             print(sub, indent + 1, fmt)
        //         }
        //         g @ Goal::Binary(name, box g1, box g2, _, _) => {
        //             for _ in 0..indent {
        //                 fmt.write_str("  ")?
        //             }
        //             let Endpoints(start, end) = g.overall_goal();

        //             fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, name))?;
        //             Ok(print(g1, indent + 1, fmt)? || print(g2, indent + 1, fmt)?)
        //         }
        //     }
        // };
        // print(self, 0, fmt).map(|b| ())

        // let Endpoints(os, oe) = self.overall_goal();
        // fmt.write_fmt(format_args!("Overall Goal: {:?} -> {:?}\n", os, oe))?;
        // if let Goal::Resolved(p) = self {
        //     fmt.write_str("there")?;
        //     fmt.write_fmt(format_args!("Solved: {:?}\n", p))
        // } else {
        //     fmt.write_str("here")?;
        //     match self {
        //         Goal::Active(_, _) => fmt.write_str("active"),
        //         Goal::Resolved(_) => fmt.write_str("resolved"),
        //         Goal::Unary(_, _, _) => fmt.write_str("unary"),
        //         Goal::Binary(_, _, _, _) => fmt.write_str("binary"),
        //     }?;
        //     if let Some((start, end)) = self.active_goal() {
        //         fmt.write_fmt(format_args!("Current Goal: {:?} -> {:?}", start, end))
        //     } else {
        //         panic!("wtf")
        //     }
        // }
    }
}

// #[derive(Debug,Clone)]
// pub enum Context {
//     Empty,
//     Cons(Path, Rc<Context>),
// }

// #[derive(Debug,Clone)]
// pub enum ContextSpec {
//     Empty,
//     Cons(Endpoints<Func>, Rc<ContextSpec>),
// }

// #[derive(Debug,Clone)]
// pub enum ContextTransform {
//     PushRefl(Func, Context),
//     Symm(Path, Context),
//     ExtendPath(Path, Path, Context),
//     Concat(Path, Path, Context),
// //    Induction(Func, Func, Func, )
// }

// enum Side {
//     Left,
//     Right,
// }

// impl ContextTransform {
//     //   pub  fn lhs(self)-> Context {}
//     //     pub fn rhs(self)-> Context {}

//     pub fn side(self, side: Side) -> Context {
//         match self {
//             ContextTransform::PushRefl(f, ctx) => match side {
//                 Side::Left => ctx,
//                 Side::Right => cons(Path::validate(PView::Refl(f)), ctx)
//             },
//             ContextTransform::Symm(p, ctx) => match side {
//                 Side::Left => cons(p, ctx),
//                 Side::Right => cons(Path::validate(PView::Inverse(Box::new(p))), ctx),
//             },
//             ContextTransform::ExtendPath(new_path, head_path, ctx) => match side {
//                 Side::Left => cons(head_path, ctx),
//                 Side::Right => {
//                     cons(Path::validate(PView::Concat(Box::new(head_path), Box::new(new_path))), ctx)
//                 }
//             },
//             ContextTransform::Concat(car, car_cdr, cdr_cdr) => match side {
//                 Side::Left => cons(car, cons(car_cdr, cdr_cdr)),
//                 Side::Right => {
//                     cons(Path::validate(PView::Concat(Box::new(car), Box::new(car_cdr))), cdr_cdr)
//                 }
//             }
//         }
//     }
// }

// #[derive(Clone,Debug)]
// pub enum ContextTransformFactory {
//     PushRefl(Func, ContextSpec),
//     Symm(Endpoints<Func>, ContextSpec),
//     ExtendPath(Path, Endpoints<Func>, ContextSpec),
//     Concat(Endpoints<Func>, Endpoints<Func>, ContextSpec),
// }

// impl ContextTransformFactory {
//     pub fn from_lhs(self, mut ctx:Context) -> Option<ContextTransform> {
//         match self {
//             Self::PushRefl(f, _) => Some(ContextTransform::PushRefl(f, ctx)),
//             Self::Symm(_, _) => Some(ContextTransform::Symm(ctx.pop_front().unwrap(), ctx)),
// Self::            ExtendPath(p, _, _) =>
//     Some(ContextTransform::ExtendPath(p, ctx.pop_front().unwrap(), ctx))
// ,
// Self::            Concat(_, _, _) =>
//     Some(ContextTransform::Concat(ctx.pop_front().unwrap(), ctx.pop_front().unwrap(), ctx)),
//         }
//     }

//     pub fn lhs_spec(&self) -> Option<ContextSpec> {
//         match self {
//             Self::PushRefl(f, ctx) => Some(ctx.clone()),
//             Self::Symm(ep, ctx) => Some(cons(ep.clone(), ctx.clone())),
//             Self::            ExtendPath(_, ep, ctx) => Some(cons(ep.clone(), ctx.clone())),
//             Self::            Concat(ab, bc, ctx) => Some(cons(ab.clone(), cons(bc.clone(), ctx.clone()))),

//         }
//     }

// }

// #[derive(Clone,Debug)]
// pub enum ContextTransformFactoryFamily {
//     PushRefl,
//     Symm,
//     ReduceRight,
//     Cut(Func),
//     Induction,
// }

// impl ContextTransformFactoryFamily {
//     pub fn from_rhs(self, mut spec : ContextSpec) -> Option<ContextTransformFactory> {
//         match self {
//             Self::PushRefl => {
//                 if let Some(ep) = spec.pop_front() {
//                                         if ep.start().syntax_eq(ep.end()) {
//                         return Some(ContextTransformFactory::PushRefl(ep.start().clone(), spec))
//                     }
//                 }
//                 None
//             }
//             Self::Symm => {
//                 if let Some(ep) = spec.pop_front() {
//                     return Some(ContextTransformFactory::Symm(Endpoints(ep.end().clone(), ep.start().clone()), spec))
//                 }
//                 None
//             }
//             Self::ReduceRight => {
//                 if let Some(Endpoints(left, right)) = spec.pop_front() {
//                     let path_to_reduced = rewrite::reduce_fully(right);
//                     let reduced = path_to_reduced.endpoints().end().clone();
//                     return Some(ContextTransformFactory::ExtendPath(Path::validate(PView::Inverse(Box::new(path_to_reduced))), Endpoints(left, reduced), spec))
//                 }
//                 None
//             }
//             Self::Cut(mid) => {
//                 if let Some(Endpoints(left, right)) = spec.pop_front() {
//                     return Some(ContextTransformFactory::Concat(Endpoints(left, mid.clone()), Endpoints(mid, right), spec))
//                 }
//                 None
//             }
//             Self::Induction => {
//                 if let Some(Endpoints(left, right)) = spec.pop_front() {
//                     if let FView::Rec(z_case, s_case) = right {
//                         return Some(ContextTransformFactory::Induction(left, z_case, s_case, spec))
//                     }
//                 }
//                 None
//             }
//         }
//     }
// }

// #[derive(Clone, Debug)]
// pub struct Tactic(View);

// #[derive(Clone, Debug)]
// pub enum View {
//     // (f, f', g) -> (f ~ f') -> ((f g) ~ (f' g))
//     CompLeft(Func, Func, Func),

//     // (f, g, g') -> (g ~ g') -> ((f g) ~ (f g'))
//     CompRight(Func, Func, Func),
// }

// enum Side {
//     Left,
//     Right,
// }

// impl Tactic {
//     pub fn view(&self) -> &View {
//         &self.0
//     }

//     pub fn into_view(self) -> View {
//         self.0
//     }

//     // pub fn endpoints(&self) -> Endpoints {
//     //     match self.view() {
//     //         View::CompLeft(f, f_, g) => Endpoints(Func::comp(f.clone(), g.clone()).unwrap(), Func::comp(f_.clone(), g.clone()).unwrap()),
//     //         View::CompRight(f, g, g_) => Endpoints(Func::comp(f.clone(), g.clone()).unwrap(), Func::comp(f.clone(), g_.clone()).unwrap()),
//     //     }
//     // }

//     // pub fn subgoals(&self) -> Vec<Endpoints> {
//     //     match self {
//     //         View::CompLeft(f, f_, _) => vec![Endpoints(f.clone(), f_.clone())],
//     //         View::CompRight(f, g, g_) => vec![Endpoints(g.clone(), g_.clone())],
//     //     }
//     // }

//     pub fn name(&self) -> &'static str {
//         match self.view() {
//             View::CompLeft(_, _, _) => "comp_left",
//             View::CompRight(_, _, _) => "comp_right",
//         }
//     }

//     fn try_side(self, side: Side) -> Result<Endpoints<Func>, BadFunc> {
//         match self.into_view() {
//             View::CompLeft(f, f_, g) => match side {
//                 Side::Left => Ok(Endpoints(f, f_)),
//                 Side::Right => Ok(Endpoints(Func::comp(f, g.clone())?, Func::comp(f_, g)?)),
//             },
//             View::CompRight(f, g, g_) => match side {
//                 Side::Left => Ok(Endpoints(g, g_)),
//                 Side::Right => Ok(Endpoints(Func::comp(f.clone(), g)?, Func::comp(f, g_)?)),
//             },
//         }
//     }

//     pub fn lhs(self) -> Endpoints<Func> {
//         self.try_side(Side::Left).expect("validated on creation")
//     }

//     pub fn rhs(self) -> Endpoints<Func> {
//         self.try_side(Side::Right).expect("validated on creation")
//     }
// }

// pub enum PathView {
//     // (p : (f ~ g)) -> (p ~ p)
//     Refl(rewrite::Path),
//     Concat(Box<Path>, Box<Path>),
//     Inverse(Box<Path>),
// }

// pub struct Path(PathView);

// impl Path {
//     pub fn validate(v: PathView) -> Path {
//         if let PathView::Concat(p1, p2) = v {
//             let Endpoints(_, p1_end) = p1.endpoints();
//             let Endpoints(p2_start, _) = p2.endpoints();

//             if !p1.endpoints().end().syntax_eq(p2.endpoints().start()) {
//                 panic!("vewwy bad")
//             }
//             Path(PathView::Concat(p1, p2))
//         } else {
//             Path(v)
//         }
//     }

//     pub fn view(&self) -> &PathView {
//         &self.0
//     }

//     pub fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
//         match self.view() {
//             PathView::Refl(rw) => Endpoints(rw.endpoints(), rw.endpoints()),
//             PathView::Concat(p1, p2) => {
//                 let Endpoints(p1_start, _) = p1.endpoints();
//                 let Endpoints(_, p2_end) = p2.endpoints();
//                 Endpoints(p1_start, p2_end)
//             }
//             PathView::Inverse(p) => {
//                 let Endpoints(start, end) = p.endpoints();
//                 Endpoints(end, start)
//             }
//         }
//     }
// }

// // pub enum Factory {
// //     Refl,
// //     Symm,
// //     Rewrite(rewrite::Factory),
// //     // CompLeft,
// //     // CompRight,
// // }

// // impl Factory {
// //     pub fn from_endpoints(self, Endpoints(start, end): Endpoints) -> Option<Tactic> {
// //         match self {
// //             Factory::Refl => {
// //                 if start.syntax_eq(&end) {
// //                     Some(Tactic::Refl(start))
// //                 } else {
// //                     None
// //                 }
// //             }
// //             Factory::Symm => Some(Tactic::Symm(start, end)),
// //             Factory::Rewrite(rwf) => {
// //                 if let Some(rw) = rwf.for_func(&end) {
// // Some(                    Tactic::Rewrite(start, rw))
// //                 } else {
// //                     None
// //                 }
// //             }
// //         }
// //     }
// // }

// // pub fn reduce(func : &Func) -> Goal {
// //     if let Some(rw) = rewrite::Factory::CompAssocFwd.for_func(func) {
// //         Goal(func)
// //     }
// // }

// // trait Tactic {
// //     fn endpoints(&self) -> Endpoints;
// //     fn subgoals(&mut self) -> Vec<&mut Goal>;
// // }

// // trait Factory {
// //     type T : Tactic;
// //     fn from_endpoints(endpoints: Endpoints) -> Option<Self::T>;
// // }

// // struct Refl(Func);

// // impl Refl {
// //     fn new(f : Func) -> Self {Self(f)}
// // }

// // impl Tactic for Refl {
// //     fn endpoints(&self)-> Endpoints {
// //         let Refl(f) = self;
// //         Endpoints(f.clone(), f.clone())
// //     }

// //     fn subgoals(&mut self) -> Vec<&mut Goal> {
// //         vec![]
// //     }
// // }

// // impl Factory for Refl {
// // type  T = Refl;
// //     fn from_endpoints(Endpoints(start, end): Endpoints) -> Option<Self::T> {
// //         if start.syntax_eq(&end) {
// //             Some(Refl(start))
// //         } else {
// //             None
// //         }
// //     }
// // }

// // pub struct Symm(Func, Func, Goal);

// // impl Symm {
// //     pub fn new(f : Func, g: Func) -> Self {Self(f.clone(), g.clone(), Goal::Active(g, f))}

// //     // fn from_goal(Endpoints(start, end):Endpoints) -> Self {

// //     // }
// // }

// // impl Tactic for Symm {
// //     fn endpoints(&self)-> Endpoints {
// //         let Self(f, g, _) = self;
// //         Endpoints(f.clone(), g.clone())
// //     }

// //     fn subgoals<'a>(&'a mut self) -> Vec<&'a mut Goal> {
// //         let Self(_, _, subgoal) = self;
// //         vec![subgoal]
// //     }
// // }

// // impl Factory for Symm {
// // type  T = Symm;
// //     fn from_endpoints(Endpoints(start, end): Endpoints) -> Option<Self::T> {
// //         Some(Self::new(start, end))
// //     }
// // }

// // pub struct RewriteFactory (pub rewrite::RuleFactory);

// // impl Factory for RewriteFactory {
// //     type T = Rewrite;
// //     fn from_endpoints(self, Endpoints(start, end): Endpoints) -> Option<Self::T> {

// //         Some(Self::new(start, end))
// //     }
// // }

// // struct Rewrite (
// //     rewrite::Rule,
// // );

// // impl Tactic for Rewrite {
// //     fn endpoints(&self)-> Endpoints {
// //         let Self(rule) = self;
// //         Endpoints(rule.clone().lhs(), rule.clone().rhs())
// //     }

// //     fn subgoals<'a>(&'a mut self) -> Vec<&'a mut Goal> {
// //         vec![]
// //     }
// // }

// // Path 1.
// //
// // - Id(f): f
// //   - Fwd needs: N/A
// //   - Rev needs: ()
// // - CompAssoc(f, g, h): ((f g) h) -> (f (g h))
// //   - Fwd needs: ()
// //   - Rev needs: ()
// // - SkipStack(arity, car, cdr): ((skip arity) (stack car cdr)) -> cdr
// //   - Fwd needs: ()
// //   - Rev needs: (arity, car)
// // - RecZ(z_case, s_case): ((rec z_case s_case) Z) -> z_case
// //   - Fwd needs: ()
// //   - Rev needs: (s_case)

// // Path 2.
// //
// // - Refl(f): (f ~ f)
// //   - Fwd needs: N/A
// //   - Rev needs: ()
// // - Symm(f, g): (f ~ g) -> (g ~ f)
// //   - Fwd needs: ()
// //   - Rev needs: ()
// // - Lift(f, g, h, path1 : (f -> g)): (f ~ h) -> (g ~ h)
// //   - Fwd needs: (path1)
// //   - Rev needs: (path1)
// // - CompLeft: (f, f', g) -> (f ~ f') -> ((f g) ~ (f' g))
// //   - Rev: ((f g) ~ (f' g)) -> () -> (f ~ f')
// //
// // Goal is

// // ProtoTrans(g).needs
// //

// // 3-Path
// //
// // Refl: (f, g, p : (f ~ g)) -> (p ~ p)
// // Trans: (f, g, h, i, j, p: (i ~ j)) -> ((f ~ g) -> (h ~ i)) -> ((f ~ g) -> (h ~ j))
// // - Rev: ((f ~ g) -> (h ~ j)) -> (i ~ j) -> ((f ~ g) -> (h ~ j))
// //
// // Goal becomes: refl ->
