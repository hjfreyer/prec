#[macro_use]
mod func;
mod base;
mod goal;
mod metapath;
mod rewrite;
mod tactics;
use crate::base::{Endpoints, SyntaxEq};
use crate::func::{Func, View};
use crate::rewrite::factory::Factory;
use crate::rewrite::Rewrite;
use im;
use im::vector::Vector;
// #![feature(
//     box_syntax,
//     box_patterns,
//     or_patterns,
//     label_break_value,
//     bindings_after_at
// )]
// #![allow(dead_code, unused_variables)]

// use std::fmt;

// #[derive(Clone, PartialEq, Eq)]
// struct FnMeta {
//     alias: Option<&'static str>,
//     int: Option<i32>,
// }

// impl FnMeta {
//     const NONE: FnMeta = FnMeta {
//         alias: None,
//         int: None,
//     };
// }

// #[derive(Clone)]
// enum Fn {
//     Z(FnMeta),
//     S(FnMeta),
//     Proj(usize, usize, FnMeta),
//     Comp(Box<Fn>, FnMatrix, FnMeta),
//     Rec(Box<Fn>, Box<Fn>, FnMeta),
// }

// #[derive(Debug)]
// enum BadFn {
//     SelectOutOfBounds(Fn),
//     ArityMismatch(Fn),
//     MatrixArityMismatch(FnMatrix),
// }

// impl Fn {
//     pub fn z() -> Fn {
//         Fn::Z(FnMeta::NONE)
//     }
//     pub fn s() -> Fn {
//         Fn::S(FnMeta::NONE)
//     }
//     pub fn proj(selector: usize, arity: usize) -> Fn {
//         Fn::Proj(selector, arity, FnMeta::NONE)
//     }
//     // Panics if gs is empty.
//     pub fn comp(f: Fn, gs: &[Fn]) -> Fn {
//         let head = gs.get(0).expect("Empty slice passed to Fn::comp");
//         let head_arity = head.arity().expect("Invalid function passed to helper.");
//         Fn::Comp(box f, FnMatrix::new(head_arity, gs), FnMeta::NONE)
//     }
//     pub fn mk_const(arity: usize, f: Fn) -> Fn {
//         Fn::Comp(box f, FnMatrix::Empty(arity), FnMeta::NONE)
//     }
//     pub fn rec(f: Fn, g: Fn) -> Fn {
//         Fn::Rec(box f, box g, FnMeta::NONE)
//     }
//     pub fn alias(name: &'static str, f: Fn) -> Fn {
//         set_meta(
//             f,
//             FnMeta {
//                 alias: Some(name),
//                 int: None,
//             },
//         )
//     }
//     pub fn int(value: i32) -> Fn {
//         let mut res: Fn = Fn::Z(FnMeta {
//             alias: None,
//             int: Some(0),
//         });
//         for ii in 0..value {
//             res = Fn::Comp(
//                 box Fn::S(FnMeta::NONE),
//                 FnMatrix::new(0, &[res]),
//                 FnMeta {
//                     alias: None,
//                     int: Some(ii + 1),
//                 },
//             );
//         }
//         res
//     }

//     fn arity(&self) -> Result<usize, BadFn> {
//         match self {
//             Fn::Z(_) => Ok(0),
//             Fn::S(_) => Ok(1),
//             &Fn::Proj(select, arity, _) => {
//                 if select < arity {
//                     Ok(arity)
//                 } else {
//                     Err(BadFn::SelectOutOfBounds(self.clone()))
//                 }
//             }
//             Fn::Comp(box f, gs, _) => {
//                 if f.arity()? == gs.len() {
//                     gs.arity()
//                 } else {
//                     Err(BadFn::ArityMismatch(self.clone()))
//                 }
//             }
//             Fn::Rec(box f, box g, _) => {
//                 let f_arity = f.arity()?;
//                 if f_arity + 2 != g.arity()? {
//                     Err(BadFn::ArityMismatch(self.clone()))
//                 } else {
//                     Ok(f_arity + 1)
//                 }
//             }
//         }
//     }

//     fn syntax_eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (Fn::Z(_), Fn::Z(_)) => true,
//             (Fn::Z(_), _) => false,
//             (Fn::S(_), Fn::S(_)) => true,
//             (Fn::S(_), _) => false,
//             (Fn::Proj(s_select, s_arity, _), Fn::Proj(o_select, o_arity, _)) => {
//                 s_select == o_select && s_arity == o_arity
//             }
//             (Fn::Proj(_, _, _), _) => false,
//             (Fn::Comp(box s_f, s_gs, _), Fn::Comp(box o_f, o_gs, _)) => {
//                 s_f.syntax_eq(o_f) && s_gs.syntax_eq(o_gs)
//             }
//             (Fn::Comp(_, _, _), _) => false,
//             (Fn::Rec(box s_f, s_g, _), Fn::Rec(box o_f, o_g, _)) => {
//                 s_f.syntax_eq(o_f) && s_g.syntax_eq(o_g)
//             }
//             (Fn::Rec(_, _, _), _) => false,
//         }
//     }
// }

// const UNPACK_META: bool = false;

// impl fmt::Debug for Fn {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         fn meta_or<F>(f: &mut fmt::Formatter<'_>, meta: &FnMeta, els: F) -> fmt::Result
//         where
//             F: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
//         {
//             if UNPACK_META {
//                 els(f)
//             } else {
//                 match meta {
//                     FnMeta {
//                         alias: Some(name),
//                         int: _,
//                     } => f.write_str(name),
//                     FnMeta {
//                         alias: None,
//                         int: Some(value),
//                     } => f.write_fmt(format_args!("{}", value)),
//                     FnMeta {
//                         alias: None,
//                         int: None,
//                     } => els(f),
//                 }
//             }
//         }
//         match &self {
//             Fn::Z(meta) => meta_or(f, meta, |f| f.write_str("Z")),
//             Fn::S(meta) => meta_or(f, meta, |f| f.write_str("S")),
//             Fn::Proj(select, _, meta) => {
//                 meta_or(f, meta, |f| f.write_fmt(format_args!("P[{}]", select)))
//             }
//             Fn::Rec(fr, g, meta) => meta_or(f, meta, |f| {
//                 f.write_fmt(format_args!("Rec[{:?}, {:?}]", fr, g))
//             }),
//             Fn::Comp(box fun, FnMatrix::Empty(arity), meta) => meta_or(f, meta, |f| {
//                 f.write_fmt(format_args!("(const {} {:?})", arity, fun))
//             }),
//             Fn::Comp(box fun, gs, meta) => meta_or(f, meta, |f| {
//                 f.write_str("(")?;

//                 f.write_fmt(format_args!("{:?}", fun))?;
//                 for g in gs {
//                     f.write_str(" ")?;
//                     f.write_fmt(format_args!("{:?}", g))?;
//                 }

//                 f.write_str(")")
//             }),
//         }
//     }
// }

// macro_rules! prec {
//     (Z) => {Fn::z()};
//     (S) => {Fn::s()};
//     ((int $value:tt)) => {Fn::int($value)};
//     ((rec $f:tt $g:tt)) => {
//         Fn::rec(prec![$f], prec![$g])
//     };
//     ((raw $v:expr)) => {$v};
//     ((proj $select:tt $arity:tt)) => {
//         Fn::proj($select, $arity)
//     };
//     ((const $arity:tt $f:tt)) => {
//         Fn::mk_const($arity, prec![$f])
//     };
//     (($f:tt $($gs:tt)+)) => {
//         Fn::comp(prec![$f], &[$(prec![$gs]),+])
//     };
//     ($f:ident) => {$f.clone()};
// }

// macro_rules! define_prec {
//     ($(let $name:ident = $fun:tt;)*) => {
//         $(
//             let $name = Fn::alias(stringify!($name), prec!($fun));
//         )*
//     };
// }

// #[derive(Clone, Debug)]
// enum FnMatrix {
//     Empty(usize),
//     Cons(Box<Fn>, Box<FnMatrix>),
// }

// impl FnMatrix {
//     fn len(&self) -> usize {
//         return self.into_iter().count();
//     }

//     fn new(arity: usize, fns: &[Fn]) -> FnMatrix {
//         if fns.is_empty() {
//             FnMatrix::Empty(arity)
//         } else {
//             FnMatrix::Cons(box fns[0].clone(), box FnMatrix::new(arity, &fns[1..]))
//         }
//     }

//     fn cons(f: Fn, gs: FnMatrix) -> Result<Self, BadFn> {
//         if f.arity()? != gs.arity()? {
//             // Bad error.
//             return Err(BadFn::ArityMismatch(f));
//         }
//         Ok(FnMatrix::Cons(box f, box gs))
//     }

//     fn get(&self, idx: usize) -> Option<&Fn> {
//         match self {
//             FnMatrix::Empty(_) => None,
//             FnMatrix::Cons(box car, _) if idx == 0 => Some(car),
//             FnMatrix::Cons(_, box cdr) => cdr.get(idx - 1),
//         }
//     }

//     fn map<F: ::std::ops::Fn(&Fn) -> Fn>(&self, arity: usize, mapper: F) -> FnMatrix {
//         match self {
//             FnMatrix::Empty(_) => FnMatrix::Empty(arity),
//             FnMatrix::Cons(box f, box cdr) => {
//                 FnMatrix::Cons(box mapper(f), box cdr.map(arity, mapper))
//             }
//         }
//     }

//     fn eye(arity: usize) -> Self {
//         let mut res = FnMatrix::Empty(arity);
//         for i in (0..arity).rev() {
//             res = FnMatrix::Cons(box Fn::Proj(i, arity, FnMeta::NONE), box res)
//         }
//         res
//     }

//     fn z(arity: usize) -> Self {
//         let z = Fn::mk_const(arity - 1, Fn::z());
//         let eye = FnMatrix::eye(arity - 1);
//         FnMatrix::Cons(box z, box eye)
//     }

//     fn s(arity: usize) -> Self {
//         let s = Fn::comp(Fn::s(), &[Fn::proj(0, arity)]);
//         let mut eye = FnMatrix::Empty(arity);
//         for i in (1..arity).rev() {
//             eye = FnMatrix::Cons(box Fn::proj(i, arity), box eye)
//         }
//         FnMatrix::Cons(box s, box eye)
//     }

//     fn arity(&self) -> Result<usize, BadFn> {
//         match self {
//             FnMatrix::Empty(arity) => Ok(*arity),
//             FnMatrix::Cons(box f, box cdr) => {
//                 let f_arity = f.arity()?;
//                 let cdr_arity = cdr.arity()?;
//                 if f_arity == cdr_arity {
//                     Ok(f_arity)
//                 } else {
//                     Err(BadFn::MatrixArityMismatch(self.clone()))
//                 }
//             }
//         }
//     }

//     fn apply_to_index<E, F: ::std::ops::Fn(Fn) -> Result<Fn, E>>(
//         self,
//         index: usize,
//         mapper: F,
//     ) -> Result<Option<Self>, E> {
//         match (index, self) {
//             (0, FnMatrix::Cons(box car, cdr)) => {
//                 Ok(Some(FnMatrix::Cons(box mapper(car)?, cdr.clone())))
//             }
//             (n, FnMatrix::Cons(box car, box cdr)) => Ok(cdr
//                 .apply_to_index(n - 1, mapper)?
//                 .map(|cdr| FnMatrix::Cons(box car.clone(), box cdr))),
//             (_, FnMatrix::Empty(_)) => Ok(None),
//         }
//     }

//     fn replace(&self, index: usize, f: Fn) -> Option<Self> {
//         match (index, self) {
//             (0, FnMatrix::Cons(box car, cdr)) => Some(FnMatrix::Cons(box f, cdr.clone())),
//             (n, FnMatrix::Cons(box car, box cdr)) => {
//                 Some(FnMatrix::Cons(box car.clone(), box cdr.replace(n - 1, f)?))
//             }
//             (_, FnMatrix::Empty(_)) => None,
//         }
//     }

//     fn syntax_eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (FnMatrix::Empty(s_arity), FnMatrix::Empty(o_arity)) => s_arity == o_arity,
//             (FnMatrix::Empty(_), _) => false,
//             (
//                 FnMatrix::Cons(box self_car, box self_cdr),
//                 FnMatrix::Cons(box other_car, box other_cdr),
//             ) => self_car.syntax_eq(other_car) && self_cdr.syntax_eq(other_cdr),
//             (FnMatrix::Cons(_, _), _) => false,
//         }
//     }

//     fn concatenate(self, other: FnMatrix) -> Result<Self, BadFn> {
//         match self {
//             FnMatrix::Empty(arity) => {
//                 if arity != other.arity()? {
//                     // Bad error.
//                     Err(BadFn::ArityMismatch(Fn::Z(FnMeta::NONE)))
//                 } else {
//                     Ok(other)
//                 }
//             }
//             FnMatrix::Cons(box car, box cdr) => {
//                 Ok(FnMatrix::Cons(box car, box cdr.concatenate(other)?))
//             }
//         }
//     }

//     fn split(self, idx: usize) -> Result<Option<(FnMatrix, Fn, FnMatrix)>, BadFn> {
//         match (idx, self) {
//             (_, FnMatrix::Empty(_)) => Ok(None),
//             (0, FnMatrix::Cons(box car, box cdr)) => {
//                 Ok(Some((FnMatrix::Empty(cdr.arity()?), car, cdr)))
//             }
//             (n, FnMatrix::Cons(box car, box cdr)) => Ok(cdr
//                 .split(n - 1)?
//                 .map(|(start, func, end)| (FnMatrix::Cons(box car, box start), func, end))),
//         }
//     }
// }

// impl<'a> IntoIterator for &'a FnMatrix {
//     type Item = &'a Box<Fn>;
//     type IntoIter = FnMatrixIterator<'a>;

//     fn into_iter(self) -> Self::IntoIter {
//         FnMatrixIterator(self)
//     }
// }

// #[derive(Clone)]
// struct FnMatrixIterator<'a>(&'a FnMatrix);

// impl<'a> Iterator for FnMatrixIterator<'a> {
//     type Item = &'a Box<Fn>;
//     fn next(&mut self) -> Option<&'a Box<Fn>> {
//         let (res, new) = match self {
//             FnMatrixIterator(FnMatrix::Empty(_)) => (None, None),
//             FnMatrixIterator(FnMatrix::Cons(f, box cdr)) => (Some(f), Some(FnMatrixIterator(cdr))),
//         };
//         if let Some(iter) = new {
//             *self = iter;
//         }
//         res
//     }
// }

// fn set_meta(func: Fn, meta: FnMeta) -> Fn {
//     match func {
//         Fn::Z(_) => Fn::Z(meta),
//         Fn::S(_) => Fn::S(meta),
//         Fn::Proj(select, arity, _) => Fn::Proj(select, arity, meta),
//         Fn::Comp(f, gs, _) => Fn::Comp(f, gs, meta),
//         Fn::Rec(f, g, _) => Fn::Rec(f, g, meta),
//     }
// }

// #[derive(Clone, Debug)]
// enum PathStep {
//     // Projection.
//     ProjElim,

//     // Composition.
//     CompDistribute,
//     EtaAbstraction,

//     // Recursion.
//     RecElimZ,
//     RecElimS,

//     // Steps in nested structures.
//     CompLeft(Box<PathStep>),
//     CompRight(usize, Box<PathStep>),
//     RecZ(Box<PathStep>),
//     RecS(Box<PathStep>),
//     Induction(Box<Path>),
// }

// #[derive(Clone, Debug)]
// enum Path {
//     Identity(Fn),
//     Step(PathStep),
//     Inverse(Box<Path>),
//     Concatenate(Box<Path>, Box<Path>),
//     // Inverse(Box<Path>),
//     // CompLeft(Fn, Box<Path>, Fn),
//     // CompRight(Fn, usize, Box<Path>, Fn),
//     // Step(Fn, Step, Fn)
// }

// impl Path {
//     fn start(&self) -> Fn {
//         match self {
//             Path::Identity(f) => f.clone(),
//             Path::Step(path, _) => path.start(),
//             Path::ExtendInverse(path, _) => path.start(),
//         }
//     }
//     fn end(&self) -> Fn {
//         match self {
//             Path::Identity(f) => f.clone(),
//             Path::Step(path, step) => {
//                 apply_step(path.end(), step.clone()).expect("Should have been sanitized")
//             }
//             Path::ExtendInverse(_, htap) => htap.start(),
//         }
//     }

//     fn step(self, step: PathStep) -> Result<Self, RewriteErr> {
//         apply_step(self.end(), step.clone())?;
//         Ok(Path::Step(box self, step))
//     }

//     fn concatenate(self, other: Self) -> Result<Self, RewriteErr> {
//         match (self, other) {
//             (Path::Identity(s_f), other) => {
//                 if s_f.syntax_eq(&other.start()) {
//                     Ok(other)
//                 } else {
//                     Err(RewriteErr::IncompatiblePaths(Path::Identity(s_f), other))
//                 }
//             }
//             (slf, Path::Identity(o_f)) => {
//                 if slf.end().syntax_eq(&o_f) {
//                     Ok(slf)
//                 } else {
//                     Err(RewriteErr::IncompatiblePaths(slf, Path::Identity(o_f)))
//                 }
//             }

//             (slf, Path::Step(box path, last_step)) => slf.concatenate(path)?.step(last_step),

//             (Path::ExtendInverse(box s_path, box s_htap), Path::ExtendInverse(box Path::Identity(o_f), box o_htap)) => {
//                     if o_htap.end().syntax_eq(&s_htap.start()) {
//                         Ok(Path::ExtendInverse(box s_path,box o_htap.concatenate(s_htap)?))
//                     } else {
//                         Err(RewriteErr::IncompatiblePaths(Path::ExtendInverse(box s_path, box s_htap), Path::ExtendInverse(box Path::Identity(o_f), box o_htap)))
//                     }
//             }
//             (slf, Path::ExtendInverse(box o_path, box o_htap)) => {
//                 Ok(Path::ExtendInverse(           box     slf.concatenate(o_path)?, box o_htap))
//             }
//         }
//     }

//     fn inverse(self) -> Self {
//         let end = self.end();
//         match self {
//             slf @ Path::Identity(_) => slf,
//             Path::Step(box path, step) => {
//                 let prev_end = path.end();
//                 Path::ExtendInverse(
//                     box Path::Identity(end),
//                     box Path::Identity(prev_end).step(step).unwrap(),
//                 )
//                 .concatenate(path.inverse())
//                 .unwrap()
//             } //path.inverse()
//             //                Path::Identity(_)

//             //            Path::ExtendInverse(box Path::Identity(_), box htap) => htap,
//             Path::ExtendInverse(box path, box htap) => {
//                 htap.inverse().concatenate(path.inverse()).unwrap()
//             }
//         }
//     }

//     fn comp_left(self, args: FnMatrix) -> Result<Self, RewriteErr> {
//         if self.start().arity()? != args.len() {
//             return Err(RewriteErr::BadFn(BadFn::ArityMismatch(Fn::Comp(
//                 box self.start(),
//                 args,
//                 FnMeta::NONE,
//             ))));
//         }

//         match self {
//             Path::Identity(f) => Ok(Path::Identity(Fn::Comp(box f, args, FnMeta::NONE))),
//             Path::Step(box path, step) => path.comp_left(args)?.step(PathStep::CompLeft(box step)),
//             Path::ExtendInverse(box path, box htap) => Ok(Path::ExtendInverse(
//                 box path.comp_left(args.clone())?,
//                 box htap.comp_left(args)?,
//             )),
//         }
//     }

//     fn comp_right(self, func: Fn, before: FnMatrix, after: FnMatrix) -> Result<Self, RewriteErr> {
//         match self {
//             Path::Identity(f) => {
//                 let composed = Fn::Comp(
//                     box func,
//                     before.concatenate(FnMatrix::cons(f, after)?)?,
//                     FnMeta::NONE,
//                 );
//                 composed.arity()?;
//                 Ok(Path::Identity(composed))
//             }
//             Path::Step(box path, step) => {
//                 let arg_idx = before.len();
//                 path.comp_right(func, before, after)?
//                     .step(PathStep::CompRight(arg_idx, box step))
//             }
//             Path::ExtendInverse(box path, box htap) => Ok(Path::ExtendInverse(
//                 box path.comp_right(func.clone(), before.clone(), after.clone())?,
//                 box htap.comp_right(func, before, after)?,
//             )),
//         }
//         // if self.start().arity()? != args.len() {
//         //     return Err(RewriteErr::BadFn(BadFn::ArityMismatch(Fn::Comp(
//         //         box self.start(),
//         //         args,
//         //         FnMeta::NONE,
//         //     ))));
//         // }

//         // let mk_err = || RewriteErr::IncompatibleFunctionAndPath(func.clone(), p.clone());
//         // if let Fn::Comp(f, gs, _) = func {
//         //     let at_idx = gs.get(idx).ok_or_else(mk_err)?;

//         //     if at_idx.syntax_eq(p.start()) {
//         //         return Ok(Path::CompRight(
//         //             func.clone(),
//         //             idx,
//         //             box p.clone(),
//         //             Fn::Comp(
//         //                 f.clone(),
//         //                 gs.replace(idx, p.end().clone())
//         //                     .expect("We just checked that at_idx is in bounds"),
//         //                 FnMeta::NONE,
//         //             ),
//         //         ));
//         //     }
//         // }

//         // return Err(mk_err());
//     }

//     fn rec_z(self, s_case: Fn) -> Result<Self, RewriteErr> {
//         if self.start().arity()? + 2 != s_case.arity()? {
//             return Err(RewriteErr::BadFn(BadFn::ArityMismatch(Fn::Rec(
//                 box self.start(),
//                 box s_case,
//                 FnMeta::NONE,
//             ))));
//         }

//         match self {
//             Path::Identity(f) => Ok(Path::Identity(Fn::Rec(box f, box s_case, FnMeta::NONE))),
//             Path::Step(box path, step) => path.rec_z(s_case)?.step(PathStep::RecZ(box step)),
//             Path::ExtendInverse(box path, box htap) => Ok(Path::ExtendInverse(
//                 box path.rec_z(s_case.clone())?,
//                 box htap.rec_z(s_case)?,
//             )),
//         }
//     }

//     fn rec_s(self, z_case: Fn) -> Result<Self, RewriteErr> {
//         if z_case.arity()? + 2 != self.start().arity()? {
//             return Err(RewriteErr::BadFn(BadFn::ArityMismatch(Fn::Rec(
//                 box z_case,
//                 box self.start(),
//                 FnMeta::NONE,
//             ))));
//         }

//         match self {
//             Path::Identity(f) => Ok(Path::Identity(Fn::Rec(box z_case, box f, FnMeta::NONE))),
//             Path::Step(step) => Ok(PathStep::RecS(box step)),
//             Path::Inverse(box htap) => Ok(Path::Inverse(                box htap.rec_s(z_case)?            )),
//             Path::Concatenate(box p1, box p2) => Ok(Path::Concatenate(box p1.))
//         }
//     }

//     //     fn induction(
//     //         func: &Fn,
//     //         z_case: &Fn,
//     //         s_case: &Fn,
//     //         z_path: &Path,
//     //         s_path: &Path,
//     //     ) -> Result<Path, RewriteErr> {
//     //         let func_arity = func.arity().map_err(RewriteErr::BadFn)?;

//     //         let func_z_start = Fn::Comp(box func.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
//     //         if !z_path.start().syntax_eq(&func_z_start) {
//     //             return Err(RewriteErr::InductionZPathStartIncorrect(
//     //                 func_z_start,
//     //                 z_path.start().clone(),
//     //             ));
//     //         }
//     //         if !z_path.end().syntax_eq(z_case) {
//     //             return Err(RewriteErr::InductionZPathEndIncorrect(
//     //                 z_case.clone(),
//     //                 z_path.end().clone(),
//     //             ));
//     //         }

//     //         let func_s_start = Fn::Comp(box func.clone(), FnMatrix::s(func_arity), FnMeta::NONE);
//     //         let s_path_applied = Fn::Comp(
//     //             box s_case.clone(),
//     //             FnMatrix::Cons(box func.clone(), box FnMatrix::eye(func_arity)),
//     //             FnMeta::NONE,
//     //         );
//     //         if !s_path.start().syntax_eq(&func_s_start) {
//     //             return Err(RewriteErr::InductionSPathStartIncorrect(
//     //                 func_s_start,
//     //                 s_path.start().clone(),
//     //             ));
//     //         }

//     //         if !s_path.end().syntax_eq(&s_path_applied) {
//     //             return Err(RewriteErr::InductionSPathEndIncorrect(
//     //                 s_path_applied,
//     //                 s_path.end().clone(),
//     //             ));
//     //         }
//     //         Ok(Path::Induction(
//     //             func.clone(),
//     //             box z_path.clone(),
//     //             box s_path.clone(),
//     //             Fn::rec(z_case.clone(), s_case.clone()),
//     //         ))
//     //     }
// }

// #[derive(Debug)]
// enum RewriteErr {
//     BadFn(BadFn),
//     MisappliedRule(PathStep),
//     IncompatiblePaths(Path, Path),
//     IncompatibleFunctionAndPath(Fn, Path),
//     InductionZPathStartIncorrect(Fn, Fn),
//     InductionSPathStartIncorrect(Fn),
//     InductionZPathEndIncorrect(Fn, Fn),
//     InductionSPathEndIncorrect(Fn),
// }

// impl From<BadFn> for RewriteErr {
//     fn from(error: BadFn) -> Self {
//         RewriteErr::BadFn(error)
//     }
// }

// fn apply_step(func: Fn, st: PathStep) -> Result<Fn, RewriteErr> {
//     match (st, func) {
//         (
//             PathStep::ProjElim,
//             Fn::Comp(box Fn::Proj(select, arity, _), FnMatrix::Cons(box car, box cdr), _),
//         ) => {
//             if select == 0 {
//                 Ok(car)
//             } else {
//                 Ok(Fn::Comp(
//                     box Fn::Proj(select - 1, arity - 1, FnMeta::NONE),
//                     cdr,
//                     FnMeta::NONE,
//                 ))
//             }
//         }
//         (st @ PathStep::ProjElim, _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         (PathStep::CompDistribute, Fn::Comp(box Fn::Comp(box int_f, int_gs, _), ext_gs, _)) => {
//             let new_gs = int_gs.map(ext_gs.arity().map_err(RewriteErr::BadFn)?, |g| {
//                 Fn::Comp(box g.clone(), ext_gs.clone(), FnMeta::NONE)
//             });
//             Ok(Fn::Comp(box int_f, new_gs, FnMeta::NONE))
//         }
//         (st @ PathStep::CompDistribute, _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         // Reduces statement Pr[z_case, s_case] * (Z * (), ...b) =>
//         //     z_case * (...b)
//         (
//             PathStep::RecElimZ,
//             Fn::Comp(
//                 box Fn::Rec(z_case, _, _),
//                 FnMatrix::Cons(box Fn::Comp(box Fn::Z(_), FnMatrix::Empty(_), _), box b),
//                 _,
//             ),
//         ) => Ok(Fn::Comp(z_case, b, FnMeta::NONE)),
//         (st @ PathStep::RecElimZ, _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         // Reduces statement Pr[z_case, s_case] * (S * a, ...b) =>
//         //     s_case * (Pr[z_case, s_case] * (a, ...b), a, ...b)
//         (
//             PathStep::RecElimS,
//             Fn::Comp(
//                 box Fn::Rec(z_case, s_case, rec_meta),
//                 FnMatrix::Cons(
//                     box Fn::Comp(box Fn::S(_), FnMatrix::Cons(a, box FnMatrix::Empty(_)), _),
//                     b,
//                 ),
//                 _,
//             ),
//         ) => {
//             let decremented_args = FnMatrix::Cons(a, b);
//             let rec_call = Fn::Comp(
//                 box Fn::Rec(z_case, s_case.clone(), rec_meta),
//                 decremented_args.clone(),
//                 FnMeta::NONE,
//             );
//             Ok(Fn::Comp(
//                 s_case,
//                 FnMatrix::Cons(box rec_call, box decremented_args),
//                 FnMeta::NONE,
//             ))
//         }
//         (st @ PathStep::RecElimS, _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         (PathStep::EtaAbstraction, f) => {
//             let arity = f.arity()?;
//             Ok(Fn::Comp(box f, FnMatrix::eye(arity), FnMeta::NONE))
//         }

//         (PathStep::CompLeft(box step), Fn::Comp(box f, gs, _)) => {
//             Ok(Fn::Comp(box apply_step(f.clone(), step)?, gs, FnMeta::NONE))
//         }
//         (st @ PathStep::CompLeft(_), _) => Err(RewriteErr::MisappliedRule(st.clone())),
//         (PathStep::CompRight(idx, box step), Fn::Comp(box f, gs, _)) => Ok(Fn::Comp(
//             box f,
//             gs.apply_to_index(idx, |g| apply_step(g, step.clone()))?
//                 .unwrap(),
//             FnMeta::NONE,
//         )),
//         (st @ PathStep::CompRight(_, _), _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         (PathStep::RecZ(box step), Fn::Rec(box z_case, box s_case, _)) => Ok(Fn::Rec(
//             box apply_step(z_case, step)?,
//             box s_case,
//             FnMeta::NONE,
//         )),
//         (st @ PathStep::RecZ(_), _) => Err(RewriteErr::MisappliedRule(st.clone())),
//         (PathStep::RecS(box step), Fn::Rec(box z_case, box s_case, _)) => Ok(Fn::Rec(
//             box z_case,
//             box apply_step(s_case, step)?,
//             FnMeta::NONE,
//         )),
//         (st @ PathStep::RecS(_), _) => Err(RewriteErr::MisappliedRule(st.clone())),

//         (PathStep::Induction(box s_path), func) => {
//             let func_arity = func.arity()?;

//             if !s_path.start().syntax_eq(&Fn::Comp(
//                 box func.clone(),
//                 FnMatrix::s(func_arity),
//                 FnMeta::NONE,
//             )) {
//                 Err(RewriteErr::InductionSPathStartIncorrect(
//                     s_path.start().clone(),
//                 ))
//             } else {
//                 match s_path.end() {
//                     Fn::Comp(box s_case, FnMatrix::Cons(box f, eye), _)
//                         if f.syntax_eq(&func) && eye.syntax_eq(&FnMatrix::eye(func_arity)) =>
//                     {
//                         let z_case =
//                             Fn::Comp(box func.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
//                         Ok(Fn::Rec(box z_case, box s_case, FnMeta::NONE))
//                     }
//                     _ => Err(RewriteErr::InductionSPathEndIncorrect(s_path.end().clone())),
//                 }
//             }
//         }
//     }
// }

// // #[derive(Debug)]
// // enum Path2Step {
// //     // // z_case ~ z_case' => (rec z_case s_case) ~ (rec z_case' s_case)
// //     // RecZ(Fn),

// //     // // s_case ~ s_case' => (rec z_case s_case) ~ (rec z_case s_case')
// //     // RecS(Fn),

// //     // // (x S) ~ (fun n. s_case (x n) n) => x ~ (rec (x Z) s_case)
// //     // Induction,

// //     // f ~ f' => (f ...a) ~ (f' ...a)
// //     CompLeft(FnMatrix),

// //     // b ~ b' => (f ...a b ...c) ~ (f ...a b' ...c)
// //     CompRight(Fn, FnMatrix, FnMatrix),
// // }

// // #[derive(Debug)]
// // enum Path2 {
// //     Identity(Path),
// //     Step(Box<Path2>, Path2Step),
// //     ExtendInverse(Box<Path2>, Box<Path2>),
// // }

// // #[derive(Debug)]
// // struct Endpoints(Fn, Fn);

// // impl Path2 {
// //     // fn start(&self) -> Endpoints {
// //     //     match self {
// //     //         Path2::Identity(path) => Endpoints(path.start(), path.end()),
// //     //     }
// //     // }
// // }

// // #[derive(Debug)]
// // enum RewriteErr2 {
// //     BadFn(BadFn),
// //     MisappliedRule(Path2Step),
// //     IncompatiblePaths(Path2, Path2),
// //     IncompatibleFunctionAndPath(Fn, Path2),
// //     InductionZPathStartIncorrect(Fn, Fn),
// //     InductionSPathStartIncorrect(Fn, Fn),
// //     InductionZPathEndIncorrect(Fn, Fn),
// //     InductionSPathEndIncorrect(Fn, Fn),
// // }

// // fn apply_step2(Endpoints(start, end): Endpoints, st: Path2Step) -> Result<Endpoints, RewriteErr2> {
// // match (st, start, end) {

// // }
// // }
// //     fn start(&self) -> &Fn {
// //         match self {
// //             Path::Identity(f) => f,
// //             Path::Step(start, _, _) => start,
// //             Path::Dot(l, _) => l.start(),
// //             Path::CompLeft(start, _, _) => start,
// //             Path::CompRight(start, _, _, _) => start,
// //             Path::Induction(start, _, _, _) => start,
// //             Path::Inverse(box p) => p.end(),
// //         }
// //     }

// //     fn end(&self) -> &Fn {
// //         match self {
// //             Path::Identity(f) => f,
// //             Path::Step(_, _, end) => end,
// //             Path::Dot(_, r) => r.end(),
// //             Path::CompLeft(_, _, end) => end,
// //             Path::CompRight(_, _, _, end) => end,
// //             Path::Induction(_, _, _, end) => end,
// //             Path::Inverse(box p) => p.start(),
// //         }
// //     }

// //     fn step(func: &Fn, st: Step) -> Result<Path, RewriteErr> {
// //         match (st, func) {
// //             (
// //                 Step::ProjElim,
// //                 Fn::Comp(box Fn::Proj(select, arity, _), FnMatrix::Cons(box car, box cdr), _),
// //             ) => {
// //                 if *select == 0 {
// //                     Ok(Path::Step(func.clone(), st, car.clone()))
// //                 } else {
// //                     Ok(Path::Step(
// //                         func.clone(),
// //                         st,
// //                         Fn::Comp(
// //                             box Fn::Proj(*select - 1, *arity - 1, FnMeta::NONE),
// //                             cdr.clone(),
// //                             FnMeta::NONE,
// //                         ),
// //                     ))
// //                 }
// //             }
// //             (Step::ProjElim, _) => Err(RewriteErr::MisappliedRule(st)),

// //             (Step::CompDistribute, Fn::Comp(box Fn::Comp(box int_f, int_gs, _), ext_gs, _)) => {
// //                 let new_gs = int_gs.map(ext_gs.arity().map_err(RewriteErr::BadFn)?, |g| {
// //                     Fn::Comp(box g.clone(), ext_gs.clone(), FnMeta::NONE)
// //                 });
// //                 Ok(Path::Step(
// //                     func.clone(),
// //                     st,
// //                     Fn::Comp(box int_f.clone(), new_gs, FnMeta::NONE),
// //                 ))
// //             }
// //             (Step::CompDistribute, _) => Err(RewriteErr::MisappliedRule(st)),

// //             // Reduces statement Pr[z_case, s_case] * (Z * (), ...b) =>
// //             //     z_case * (...b)
// //             (
// //                 Step::RecElimZ,
// //                 Fn::Comp(
// //                     box Fn::Rec(z_case, _, _),
// //                     FnMatrix::Cons(box Fn::Comp(box Fn::Z(_), FnMatrix::Empty(_), _), box b),
// //                     _,
// //                 ),
// //             ) => Ok(Path::Step(
// //                 func.clone(),
// //                 st,
// //                 Fn::Comp(z_case.clone(), b.clone(), FnMeta::NONE),
// //             )),
// //             (Step::RecElimZ, _) => Err(RewriteErr::MisappliedRule(st)),

// //             // Reduces statement Pr[z_case, s_case] * (S * a, ...b) =>
// //             //     s_case * (Pr[z_case, s_case] * (a, ...b), a, ...b)
// //             (
// //                 Step::RecElimS,
// //                 Fn::Comp(
// //                     rec @ box Fn::Rec(_, s_case, _),
// //                     FnMatrix::Cons(
// //                         box Fn::Comp(box Fn::S(_), FnMatrix::Cons(a, box FnMatrix::Empty(_)), _),
// //                         b,
// //                     ),
// //                     _,
// //                 ),
// //             ) => {
// //                 let decremented_args = FnMatrix::Cons(a.clone(), b.clone());
// //                 let rec_call = Fn::Comp(rec.clone(), decremented_args.clone(), FnMeta::NONE);
// //                 Ok(Path::Step(
// //                     func.clone(),
// //                     st,
// //                     Fn::Comp(
// //                         s_case.clone(),
// //                         FnMatrix::Cons(box rec_call, box decremented_args),
// //                         FnMeta::NONE,
// //                     ),
// //                 ))
// //             }
// //             (Step::RecElimS, _) => Err(RewriteErr::MisappliedRule(st)),

// //             (Step::EtaAbstraction, f) => {
// //                 let arity = f.arity().map_err(RewriteErr::BadFn)?;
// //                 Ok(Path::Step(
// //                     func.clone(),
// //                     st,
// //                     Fn::Comp(box f.clone(), FnMatrix::eye(arity), FnMeta::NONE),
// //                 ))
// //             }

// //             (Step::EtaReduction, Fn::Comp(box f, gs, _))
// //                 if gs.syntax_eq(&FnMatrix::eye(gs.len())) =>
// //             {
// //                 Ok(Path::Step(func.clone(), st, f.clone()))
// //             }
// //             (Step::EtaReduction, _) => Err(RewriteErr::MisappliedRule(st)),
// //         }
// //     }

// //     fn dot(l: &Path, r: &Path) -> Result<Path, RewriteErr> {
// //         if l.end().syntax_eq(r.start()) {
// //             Ok(Path::Dot(box l.clone(), box r.clone()))
// //         } else {
// //             Err(RewriteErr::IncompatiblePaths(l.clone(), r.clone()))
// //         }
// //     }

// //     fn comp_left(func: &Fn, p: &Path) -> Result<Path, RewriteErr> {
// //         if let Fn::Comp(box f, gs, _) = func {
// //             if p.start().syntax_eq(f) {
// //                 return Ok(Path::CompLeft(
// //                     func.clone(),
// //                     box p.clone(),
// //                     Fn::Comp(box p.end().clone(), gs.clone(), FnMeta::NONE),
// //                 ));
// //             }
// //         }
// //         Err(RewriteErr::IncompatibleFunctionAndPath(
// //             func.clone(),
// //             p.clone(),
// //         ))
// //     }

// //     fn comp_right(func: &Fn, idx: usize, p: &Path) -> Result<Path, RewriteErr> {
// //         let mk_err = || RewriteErr::IncompatibleFunctionAndPath(func.clone(), p.clone());
// //         if let Fn::Comp(f, gs, _) = func {
// //             let at_idx = gs.get(idx).ok_or_else(mk_err)?;

// //             if at_idx.syntax_eq(p.start()) {
// //                 return Ok(Path::CompRight(
// //                     func.clone(),
// //                     idx,
// //                     box p.clone(),
// //                     Fn::Comp(
// //                         f.clone(),
// //                         gs.replace(idx, p.end().clone())
// //                             .expect("We just checked that at_idx is in bounds"),
// //                         FnMeta::NONE,
// //                     ),
// //                 ));
// //             }
// //         }

// //         return Err(mk_err());
// //     }

// //     fn induction(
// //         func: &Fn,
// //         z_case: &Fn,
// //         s_case: &Fn,
// //         z_path: &Path,
// //         s_path: &Path,
// //     ) -> Result<Path, RewriteErr> {
// //         let func_arity = func.arity().map_err(RewriteErr::BadFn)?;

// //         let func_z_start = Fn::Comp(box func.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
// //         if !z_path.start().syntax_eq(&func_z_start) {
// //             return Err(RewriteErr::InductionZPathStartIncorrect(
// //                 func_z_start,
// //                 z_path.start().clone(),
// //             ));
// //         }
// //         if !z_path.end().syntax_eq(z_case) {
// //             return Err(RewriteErr::InductionZPathEndIncorrect(
// //                 z_case.clone(),
// //                 z_path.end().clone(),
// //             ));
// //         }

// //         let func_s_start = Fn::Comp(box func.clone(), FnMatrix::s(func_arity), FnMeta::NONE);
// //         let s_path_applied = Fn::Comp(
// //             box s_case.clone(),
// //             FnMatrix::Cons(box func.clone(), box FnMatrix::eye(func_arity)),
// //             FnMeta::NONE,
// //         );
// //         if !s_path.start().syntax_eq(&func_s_start) {
// //             return Err(RewriteErr::InductionSPathStartIncorrect(
// //                 func_s_start,
// //                 s_path.start().clone(),
// //             ));
// //         }

// //         if !s_path.end().syntax_eq(&s_path_applied) {
// //             return Err(RewriteErr::InductionSPathEndIncorrect(
// //                 s_path_applied,
// //                 s_path.end().clone(),
// //             ));
// //         }
// //         Ok(Path::Induction(
// //             func.clone(),
// //             box z_path.clone(),
// //             box s_path.clone(),
// //             Fn::rec(z_case.clone(), s_case.clone()),
// //         ))
// //     }
// // }

// fn reduce_fully(f: &Fn) -> Result<Path, BadFn> {
//     f.arity()?;
//     let mut path = Path::Identity(f.clone());
//     while let Some(ext) = suggest_extension(&path.end())? {
//         path = path.concatenate(ext).map_err(|e| match e {
//             RewriteErr::BadFn(b) => b,
//             _ => panic!("bad"),
//         })?;
//     }
//     Ok(path)
// }

// fn suggest_extension(func: &Fn) -> Result<Option<Path>, BadFn> {
//     let panic_on_misapplied = |e| match e {
//         RewriteErr::BadFn(b) => b,
//         _ => panic!("Rule should never fail"),
//     };
//     macro_rules! try_step {
//         ($step:expr) => {
//             match Path::Identity(func.clone()).step($step) {
//                 Ok(p) => return Ok(Some(p)),
//                 Err(RewriteErr::BadFn(b)) => return Err(b),
//                 Err(_) => (),
//             }
//         };
//     }
//     try_step![PathStep::ProjElim];
//     try_step![PathStep::CompDistribute];
//     try_step![PathStep::RecElimZ];
//     try_step![PathStep::RecElimS];

//     if let Fn::Comp(box f, gs, _) = func {
//         if gs.syntax_eq(&FnMatrix::eye(f.arity()?)) {
//             return Ok(Some(
//                 Path::Identity(f.clone())
//                     .step(PathStep::EtaAbstraction)
//                     .map_err(panic_on_misapplied)?
//                     .inverse(),
//             ));
//         }
//     }

//     if let Fn::Comp(box Fn::Rec(_, _, _), FnMatrix::Cons(box Fn::Z(_) | box Fn::S(_), _), _) = func
//     {
//         return Path::Identity(func.clone())
//             .step(PathStep::CompRight(0, box PathStep::EtaAbstraction))
//             .map_err(panic_on_misapplied)
//             .map(|p| Some(p));
//     }

//     if let Fn::Comp(box f, gs, _) = func {
//         if let Some(ext) = suggest_extension(f)? {
//             return ext
//                 .comp_left(gs.clone())
//                 .map_err(panic_on_misapplied)
//                 .map(Some);
//         }
//         for idx in 0..gs.len() {
//             let (before, g, after) = gs.clone().split(idx)?.unwrap();
//             if let Some(ext) = suggest_extension(&g)? {
//                 return ext
//                     .comp_right(f.clone(), before, after)
//                     .map_err(panic_on_misapplied)
//                     .map(Some);
//             }
//         }
//     }

//     if let Fn::Rec(box z_case, box s_case, _) = func {
//         if let Some(ext) = suggest_extension(z_case)? {
//             return ext
//                 .rec_z(s_case.clone())
//                 .map_err(panic_on_misapplied)
//                 .map(Some);
//         }
//         if let Some(ext) = suggest_extension(s_case)? {
//             return ext
//                 .rec_s(z_case.clone())
//                 .map_err(panic_on_misapplied)
//                 .map(Some);
//         }
//     }

//     Ok(None)
// }

// // fn run_test(func: &Fn) {
// //     func.arity().unwrap();
// //     reduce_fully(func).unwrap();
// // }

// fn find_path(start: &Fn, end: &Fn) -> Result<Option<Path>, BadFn> {
//     // match (start, end) {
//     //     (_, Fn::Rec(box z_case, s_case, _)) => {
//     //         if let Some(ext) = find_path_to_rec(start, z_case, s_case)? {
//     //             return Ok(Some(ext));
//     //         }
//     //     }
//     //     (Fn::Rec(box z_case, s_case, _), _) => {
//     //         if let Some(ext) = find_path_to_rec(end, z_case, s_case)? {
//     //             return Ok(Some(Path::Inverse(box ext)));
//     //         }
//     //     }
//     //     _ => (),
//     // }

//     let start_reduced = reduce_fully(start)?;
//     let end_reduced = reduce_fully(end)?;
//     println!("paths");

//     println!("{:#?}", start_reduced);
//     println!("{:#?}", end_reduced.clone().inverse());
//     if start_reduced.end().syntax_eq(&end_reduced.end()) {
//         Ok(Some(
//             Path::concatenate(start_reduced, end_reduced.inverse()).unwrap(),
//         ))
//     } else {
//         Ok(None)
//     }
// }

// // fn find_path_to_rec(func: &Fn, z_case: &Fn, s_case: &Fn) -> Result<Option<Path>, BadFn> {
// //     let start_arity = func.arity()?;
// //     let z_app = Fn::Comp(box func.clone(), FnMatrix::z(start_arity), FnMeta::NONE);
// //     let s_app = Fn::Comp(box func.clone(), FnMatrix::s(start_arity), FnMeta::NONE);

// //     let s_case_unrolled = Fn::Comp(
// //         box s_case.clone(),
// //         FnMatrix::Cons(box func.clone(), box FnMatrix::eye(start_arity)),
// //         FnMeta::NONE,
// //     );

// //     let z_path = find_path(&z_app, z_case)?;
// //     let s_path = find_path(&s_app, &s_case_unrolled)?;

// //     if let (Some(z_path), Some(s_path)) = (z_path, s_path) {
// //         Path::induction(func, z_case, s_case, &z_path, &s_path)
// //             .map(|p| Some(p))
// //             .map_err(|e| match e {
// //                 RewriteErr::BadFn(b) => b,
// //                 _ => panic!("{:?}", e),
// //             })
// //     } else {
// //         Ok(None)
// //     }
// // }

// // struct PathBuilder(Path);

// // impl PathBuilder {
// //     fn new(func: &Fn) -> Result<PathBuilder, BadFn> {
// //         func.arity()?;
// //         Ok(PathBuilder(Path::Identity(func.clone())))
// //     }

// //     fn to(self, dest: &Fn) -> Option<Self> {
// //         let PathBuilder(path) = self;
// //         if let Some(ext) = find_path(path.end(), dest).expect("bad") {
// //             return Some(PathBuilder(Path::dot(&path, &ext).expect("bad")));
// //         }
// //         return None;
// //     }

// //     fn simplify(self) -> Self {
// //         let PathBuilder(path) = self;

// //         PathBuilder(Path::dot(&path, &reduce_fully(path.end()).unwrap()).expect("bad"))
// //     }

// //     fn apply_z(self) -> Self {
// //         let PathBuilder(path) = self;
// //         let arity = path.start().arity().unwrap();
// //         let new_start = Fn::Comp(box path.start().clone(), FnMatrix::z(arity), FnMeta::NONE);
// //         let new_end = Fn::Comp(box path.end().clone(), FnMatrix::z(arity), FnMeta::NONE);
// //         PathBuilder(Path::CompLeft(new_start, box path, new_end))
// //     }
// //     fn apply_s(self) -> Self {
// //         let PathBuilder(path) = self;
// //         let arity = path.start().arity().unwrap();
// //         let new_start = Fn::Comp(box path.start().clone(), FnMatrix::s(arity), FnMeta::NONE);
// //         let new_end = Fn::Comp(box path.end().clone(), FnMatrix::s(arity), FnMeta::NONE);
// //         PathBuilder(Path::CompLeft(new_start, box path, new_end))
// //     }

// //     fn build(self) -> Path {
// //         self.0
// //     }
// // }

// struct Endpoints(Fn, Fn);

// type UnaryFn = dyn ::std::ops::Fn(Path) -> Path;
// type BinaryFn = dyn ::std::ops::Fn(Path, Path) -> Path;

// type EndpointTransform1 = dyn ::std::ops::Fn(Endpoints) -> Endpoints;
// type EndpointTransform2 = dyn ::std::ops::Fn(Endpoints, Endpoints) -> Endpoints;

// // #[derive(Debug)]
// enum Goal {
//     Active(Fn, Fn),
//     Resolved(Path),
//     Unary(
//         &'static str,
//         Box<Goal>,
//         Box<UnaryFn>,
//         Box<EndpointTransform1>,
//     ),
//     Binary(
//         &'static str,
//         Box<Goal>,
//         Box<Goal>,
//         Box<BinaryFn>,
//         Box<EndpointTransform2>,
//     ),
//     //    Cut(Box<Goal>, Box<Goal>),
//     //    Induction(Fn, Fn, Box<Goal>, Box<Goal>),
// }

// impl Goal {
//     fn new(start: Fn, end: Fn) -> Result<Self, BadFn> {
//         start.arity()?;
//         end.arity()?;
//         Ok(Self::Active(start, end))
//     }

//     fn cut(&mut self, mid: Fn) -> &mut Self {
//         let helper = |start, end| -> Goal {
//             let reduce = reduce_fully(&start).unwrap();
//             Goal::Binary(
//                 "cut",
//                 box Goal::Active(start, mid.clone()),
//                 box Goal::Active(mid, end),
//                 box |p1, p2| p1.concatenate(p2).unwrap(),
//                 box |Endpoints(start, _), Endpoints(_, end)| Endpoints(start, end),
//             )
//         };
//         self.replace_active_goal(helper)
//     }

//     fn simplify(&mut self) -> &mut Self {
//         fn helper(start: Fn, end: Fn) -> Goal {
//             let reduce = reduce_fully(&start).unwrap();
//             let mid_point = reduce.end().clone();
//             Goal::Binary(
//                 "simplify",
//                 box Goal::Resolved(reduce),
//                 box Goal::Active(mid_point, end),
//                 box |p1, p2| p1.concatenate(p2).unwrap(),
//                 box |Endpoints(start, _), Endpoints(_, end)| Endpoints(start, end),
//             )
//         }
//         self.replace_active_goal(helper)
//     }

//     fn auto(&mut self) -> &mut Self {
//         self.replace_active_goal(|start, end| {
//             if let Some(path) = find_path(&start, &end).unwrap() {
//                 Goal::Resolved(path)
//             } else {
//                 Goal::Active(start, end)
//             }
//         });
//         self.resolve()
//     }
//     fn resolve(&mut self) -> &mut Self {
//         match self {
//             Goal::Unary(_, box g1, stitcher, _) => {
//                 g1.resolve();
//                 if let Goal::Resolved(p) = g1 {
//                     *self = Goal::Resolved(stitcher(p.clone()))
//                 }
//             }
//             Goal::Binary(_, box g1, box g2, stitcher, _) => {
//                 g1.resolve();
//                 g2.resolve();
//                 if let (Goal::Resolved(p1), Goal::Resolved(p2)) = (g1, g2) {
//                     *self = Goal::Resolved(stitcher(p1.clone(), p2.clone()))
//                 }
//             }
//             _ => (),
//         };
//         self

//         //  *self =       *match self {
//         //             Goal::Resolved(_) => self,
//         //             Goal::Active(start, end) => {

//         //             }
//         //             Goal::Binary(box Goal::Resolved(p1), box i2) => match i2.auto() {
//         //                 Goal::Resolved(p2) => Goal::Resolved(Path::dot(&p1, &p2).unwrap()),
//         //                 i2 => Goal::Cut(box Goal::Resolved(p1), box i2),
//         //             },
//         //             Goal::Binary(box i1, box i2) => Goal::Cut(box i1.auto(), box i2),

//         //             Goal::Induction(start, end, box Goal::Resolved(p1), box i2) => {
//         //                 match i2.auto() {
//         //                     Goal::Resolved(p2) => {
//         //                         if let Fn::Rec(box z_case, box s_case, _) = end {
//         //                             Goal::Resolved(
//         //                                 Path::induction(&start, &z_case, &s_case, &p1, &p2).unwrap(),
//         //                             )
//         //                         } else {
//         //                             panic!("no")
//         //                         }
//         //                     }
//         //                     i2 => Goal::Induction(start, end, box Goal::Resolved(p1), box i2),
//         //                 }
//         //             }
//         //             Goal::Induction(start, end, box i1, box i2) => {
//         //                 Goal::Induction(start, end, box i1.auto(), box i2)
//         //             }
//         // }
//     }

//     // fn cut_rec(&mut self, s_case: Fn) -> &mut Self {
//     //     self.replace_active_goal(|start: Fn, end: Fn| {
//     //         let func_arity = start.arity().unwrap();
//     //         let z_case = Fn::Comp(box start.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
//     //         let new_end = Fn::Rec(box z_case, box s_case.clone(), FnMeta::NONE);

//     //         let rec_goal = Goal::Active(start, new_end.clone());
//     //         let completion_goal = Goal::Active(new_end, end);

//     //         Self::mk_cut(rec_goal, completion_goal)
//     //     })
//     // }

//     fn mk_cut(name: &'static str, g1: Goal, g2: Goal) -> Goal {
//         Goal::Binary(
//             name,
//             box g1,
//             box g2,
//             box |p1, p2| {
//                 println!("{:?}", p1.end());
//                 println!("{:?}", p2.start());
//                 p1.concatenate(p2).unwrap()
//             },
//             box |Endpoints(start, _), Endpoints(_, end)| Endpoints(start, end),
//         )
//     }

//     fn induction(&mut self, s_case: Fn) -> &mut Self {
//         self.replace_active_goal(|start: Fn, end: Fn| {
//             let func_arity = start.arity().unwrap();
//             let z_case = Fn::Comp(box start.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
//             let new_end = Fn::Rec(box z_case, box s_case.clone(), FnMeta::NONE);

//             let sub_start = Fn::Comp(box start.clone(), FnMatrix::s(func_arity), FnMeta::NONE);
//             let sub_end = Fn::Comp(
//                 box s_case.clone(),
//                 FnMatrix::Cons(box start.clone(), box FnMatrix::eye(func_arity)),
//                 FnMeta::NONE,
//             );

//             //            let bound_start = start.clone();
//             let new_end2 = new_end.clone();
//             let inductive_goal = Goal::Unary(
//                 "Induction",
//                 box Goal::Active(sub_start, sub_end),
//                 box move |p| {
//                     Path::Identity(start.clone())
//                         .step(PathStep::Induction(box p))
//                         .unwrap()
//                 },
//                 box move |Endpoints(sub_start, sub_end)| {
//                     match (sub_start, sub_end) {
//                         // Sloppy and bad
//                         (Fn::Comp(box start, _, _), _) => {
//                             Endpoints(start.clone(), new_end2.clone())
//                         }
//                         _ => panic!("not a thing"),
//                     }
//                 },
//             );

//             let completion_goal = Goal::Active(new_end, end);

//             Goal::mk_cut("induction", inductive_goal, completion_goal)

//             // if let Fn::Rec(box z_case, box s_case, _) = &end {
//             //     let arity = start.arity().unwrap();
//             //     let func_z_start = Fn::Comp(box start.clone(), FnMatrix::z(arity), FnMeta::NONE);
//             //     let i1 = Goal::Goal(func_z_start, z_case.clone());

//             //     let func_s_start = Fn::Comp(box start.clone(), FnMatrix::s(arity), FnMeta::NONE);
//             //     let s_path_applied = Fn::Comp(
//             //         box s_case.clone(),
//             //         FnMatrix::Cons(box start.clone(), box FnMatrix::eye(arity)),
//             //         FnMeta::NONE,
//             //     );

//             //     let i2 = Goal::Goal(func_s_start, s_path_applied);

//             //     Goal::Induction(start, end, box i1, box i2)
//             // } else {
//             //     Goal::Goal(start, end)
//             // }
//         })
//     }

//     fn rec(&mut self) -> &mut Self {
//         self.replace_active_goal(|start: Fn, end: Fn| match (start, end) {
//             (Fn::Rec(box z_start, box s_start, _), Fn::Rec(box z_end, box s_end, _)) => {
//                 let z_goal = Goal::Active(z_start, z_end);
//                 let s_goal = Goal::Active(s_start, s_end);

//                 Goal::Binary(
//                     "rec",
//                     box z_goal,
//                     box s_goal,
//                     box |zp, sp| {
//                         let s_start = sp.start();
//                         let z_end = zp.end();
//                         let z_replaced_path = zp.rec_z(s_start).unwrap();
//                         let both_replaced_path = sp.rec_s(z_end).unwrap();
//                         z_replaced_path.concatenate(both_replaced_path).unwrap()
//                     },
//                     box |Endpoints(z_start, z_end), Endpoints(s_start, s_end)| {
//                         Endpoints(
//                             Fn::Rec(box z_start, box s_start, FnMeta::NONE),
//                             Fn::Rec(box z_end, box s_end, FnMeta::NONE),
//                         )
//                     },
//                 )
//             }
//             (start, end) => Goal::Active(start, end),
//         })
//     }

//     fn swap(&mut self) -> &mut Self {
//         self.replace_active_goal(|start: Fn, end: Fn| {
//             let subgoal = Goal::Active(end, start);
//             Goal::Unary(
//                 "swap",
//                 box subgoal,
//                 box |p| p.inverse(),
//                 box |Endpoints(start, end)| Endpoints(end, start),
//             )
//         })
//     }

//     fn active_goal(&self) -> Option<(Fn, Fn)> {
//         match self {
//             Goal::Resolved(_) => None,
//             Goal::Active(start, end) => Some((start.clone(), end.clone())),
//             //            Goal::Cut(box i1, box i2) => i1.active_goal().or_else(|| i2.active_goal()),
//             Goal::Unary(_, box subgoal, _, _) => subgoal.active_goal(),
//             Goal::Binary(_, box g1, box g2, _, _) => g1.active_goal().or_else(|| g2.active_goal()),
//         }
//     }

//     // fn replace_active_goal<F: FnOnce(Fn, Fn) -> Goal>(self, f: F) -> Self {
//     //     enum Res<F> {
//     //         Done(Goal),
//     //         Pass(Goal, F),
//     //     }
//     //     fn helper<F: FnOnce(Fn, Fn) -> Goal>(s: Goal, f: F) -> Res<F> {
//     //         match s {
//     //             Goal::Resolved(_) => Res::Pass(s, f),
//     //             Goal::Active(start, end) => Res::Done(f(start, end)),
//     //             Goal::Cut(box i1, box i2) => match helper(i1, f) {
//     //                 Res::Done(i1) => Res::Done(Goal::Cut(box i1, box i2)),
//     //                 Res::Pass(i1, f) => match helper(i2, f) {
//     //                     Res::Done(i2) => Res::Done(Goal::Cut(box i1, box i2)),
//     //                     Res::Pass(i2, f) => panic!("no active goal"),
//     //                 },
//     //             },
//     //             Goal::Unary(box subgoal, stitch) => match helper(subgoal, f) {
//     //                 Res::Done(subgoal) => Res::Done(Goal::Unary(box subgoal, stitch)),
//     //                 Res::Pass(i2, f) => panic!("no active goal"),
//     //             },
//     //             //  Goal::Binary(box i1, box i2, stitch) => match helper(i1, f) {
//     //             //     Res::Done(i1) => Res::Done(Goal::Cut(box i1, box i2)),
//     //             //     Res::Pass(i1, f) => match helper(i2, f) {
//     //             //         Res::Done(i2) => Res::Done(Goal::Cut(box i1, box i2)),
//     //             //         Res::Pass(i2, f) => panic!("no active goal"),
//     //             //     },
//     //             // },
//     //         }
//     //     }
//     //     match helper(self, f) {
//     //         Res::Done(res) => res,
//     //         Res::Pass(_, _) => panic!("no active goal"),
//     //     }
//     // }

//     fn replace_active_goal<F: FnOnce(Fn, Fn) -> Goal>(&mut self, f: F) -> &mut Self {
//         fn helper<F: FnOnce(Fn, Fn) -> Goal>(s: &mut Goal, f: F) -> Option<F> {
//             match s {
//                 Goal::Resolved(_) => Some(f),
//                 Goal::Active(start, end) => {
//                     *s = f(start.clone(), end.clone());
//                     None
//                 }
//                 //       Goal::Cut(box i1, box i2) => helper(i1, f).and_then(|f| helper(i2, f)),
//                 Goal::Unary(_, box subgoal, _, _) => helper(subgoal, f),
//                 Goal::Binary(_, box i1, box i2, _, _) => helper(i1, f).and_then(|f| helper(i2, f)),
//             }
//         }
//         helper(self, f);
//         self
//     }

//     fn overall_goal(&self) -> Endpoints {
//         match self {
//             Goal::Resolved(path) => Endpoints(path.start(), path.end()),
//             Goal::Active(start, end) => Endpoints(start.clone(), end.clone()),
//             Goal::Unary(_, box subgoal, _, endpoint_transform) => {
//                 endpoint_transform(subgoal.overall_goal())
//             }
//             Goal::Binary(_, box g1, box g2, _, endpoint_transform) => {
//                 endpoint_transform(g1.overall_goal(), g2.overall_goal())
//             }
//         }
//     }
// }

// impl fmt::Debug for Goal {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         fn print(g: &Goal, indent: u32, fmt: &mut fmt::Formatter<'_>) -> Result<bool, fmt::Error> {
//             match g {
//                 Goal::Active(s, e) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     fmt.write_fmt(format_args!("{:?} -> {:?} ACTIVE\n", s, e))?;
//                     Ok(true)
//                 }
//                 Goal::Resolved(p) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     fmt.write_fmt(format_args!("{:?} -> {:?} DONE\n", p.start(), p.end()))?;
//                     Ok(false)
//                 }
//                 g @ Goal::Unary(name, box sub, _, _) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     let Endpoints(start, end) = g.overall_goal();
//                     fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, name))?;
//                     print(sub, indent + 1, fmt)
//                 }
//                 g @ Goal::Binary(name, box g1, box g2, _, _) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     let Endpoints(start, end) = g.overall_goal();

//                     fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, name))?;
//                     Ok(print(g1, indent + 1, fmt)? || print(g2, indent + 1, fmt)?)
//                 }
//             }
//         };
//         print(self, 0, fmt).map(|b| ())
//         // let Endpoints(os, oe) = self.overall_goal();
//         // fmt.write_fmt(format_args!("Overall Goal: {:?} -> {:?}\n", os, oe))?;
//         // if let Goal::Resolved(p) = self {
//         //     fmt.write_str("there")?;
//         //     fmt.write_fmt(format_args!("Solved: {:?}\n", p))
//         // } else {
//         //     fmt.write_str("here")?;
//         //     match self {
//         //         Goal::Active(_, _) => fmt.write_str("active"),
//         //         Goal::Resolved(_) => fmt.write_str("resolved"),
//         //         Goal::Unary(_, _, _) => fmt.write_str("unary"),
//         //         Goal::Binary(_, _, _, _) => fmt.write_str("binary"),
//         //     }?;
//         //     if let Some((start, end)) = self.active_goal() {
//         //         fmt.write_fmt(format_args!("Current Goal: {:?} -> {:?}", start, end))
//         //     } else {
//         //         panic!("wtf")
//         //     }
//         // }
//     }

//     // fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//     //     match self {

//     //             Goal::Active(_, _) => fmt.write_str("active"),
//     //             Goal::Resolved(_) => fmt.write_str("resolved"),
//     //             Goal::Unary(box g,  _,_) =>  fmt.debug_tuple("Unary").field(g).finish(),
//     //             Goal::Binary(box g1, box g2,  _,_) =>    fmt.debug_tuple("Binary")
//     //             .field(g1)
//     //             .field(g2)
//     //             .finish()
//     //     }

//     // }
// }

fn main() {
    func_let![
        let _a = ((proj 2 3) (int 0) (int 1) (int 2));
        let _t1 = ((const 3 Z) (int 0) (int 1) (int 2));
        let _t2 = ((const 3 Z) (const 2 (int 0)) (const 2 (int 1)) (const 2 (int 2)));
        let _t3 = (((proj 0 2) (proj 1 3) (proj 0 3)) (int 0) (int 1) (int 2));
        let not = (rec (int 1) (const 2 Z));


        let _t4 = (not Z);
        let _t5 = (not S);
        let _t6 = (not (const 5 Z));
        let _t7 = (not (not (const 1 (int 5))));
        let _b = ((proj 2 3) (const 0 (int 1)) (int 2) (int 3));

        let is_even = (rec (int 1) (not (proj 0 2)));
        let double = (rec (int 0) (S (S (proj 0 2))));
    ];
    //    println!("{:#?}", is_even);

    //    let g = goal::HorizontalPath::new(func![(is_even double)], func![(const 1 (int 1))]);

    //    let mut g = im::vector![Endpoints(_t4, func![(int 1)])];
    let mut g = im::vector![Endpoints(func![(is_even double)], func![(const 1 (int 1))])];

    // let tax = vec![
    //     //        tactics::Tactic::Ident,
    //     //tactics::Tactic::Cut(func![(rec (int 1) ((not not) (proj 0 2)))]),
    //     tactics::Tactic::Induction(func![((not not) (proj 0 2))]),
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::Tactic::Symm,
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::Tactic::Ident,
    //     // tactics::Tactic::Symm,
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::Tactic::Induction(func![(proj 0 2)]),
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::Tactic::Symm,
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::Tactic::Ident,
    //     // tactics::Tactic::ReduceRight,
    //     // tactics::ContextTransformFactoryFamily::PushRefl,
    // ];
    // println!("{:?}", tactics::ContextSpecWrapper(g.clone()));
    // for t in tax.into_iter() {
    //     for op in t.for_goal(&g) {
    //         g = op.reverse(g.clone()).unwrap();
    //         println!("{:?}", tactics::ContextSpecWrapper(g.clone()));
    //     }
    // }

    // println!("got here");
    // println!("{:?}", g);

    // let mut expr = _t7;
    // println!("{:?}", expr);
    // while let Some(rw) = rewrite::factory::Reduce().for_lhs(expr.clone()) {
    //     println!("{:?}", rw);

    //     if !expr.syntax_eq(&rw.clone().lhs()) {
    //         println!("wanted to match:   {:#?}", expr);
    //         println!("reduction was for: {:#?}", &rw.clone().lhs());
    //         panic!("ya done goofed")
    //     }
    //     expr = rw.rhs();
    //     println!("{:?}", expr);
    // }
    // let reduction = std::iter::successors(Some(_t6), |a| {
    //     rewrite::factory::Reduce()
    //         .for_lhs(a.clone())
    //         .map(|rw| {println!("{:?}", rw); rw.rhs()})
    // }).take(100);
    // for r in reduction {
    //     println!("{:?}", r)
    // }

    // let mut g = tactics::Goal::Active(tactics::Endpoints(func![(is_even double)], func![(const 1 (int 1))]));
    // println!("{:?}", g);
    // g.apply(tactics::Factory::Rewrite(rewrite::Factory::CompAssocFwd));
    // println!("{:?}", g);
    // let ca = rewrite::RuleFamily::match_side(rewrite::RuleFamily::CompAssoc,
    //     rewrite::Side::Left, &_a).unwrap().rhs();
    // let ca = rewrite::RuleFamily::match_side(rewrite::RuleFamily::CompAssoc,
    //     rewrite::Side::Left, &ca).unwrap().rhs();
    // println!("{:?}", ca)
    // if let View::Comp(f, g) = ca.image().view() {
    //     println!("{:?}", g);
    //     let gg = rewrite::SkipStack::from_preimage(g).unwrap().image();
    //     println!("{:?}", gg);
    // }
    // let z1 = func::View::Z;
    // let z2 = func::View::Z;

    // let s1 = func::View::Stack(&z1, &z1);
    // let s2 = func::View::Stack(&z2, &z2);

    // println!("{}", s1 == s2)
    //     define_prec![

    //

    //                 let double = (rec (int 0) (S (S (proj 0 2))));
    //                 let maybe_increment = (rec (proj 0 1) (S (proj 2 3)));
    //     //            let plus_mod2 = (rec (int 0) (not (proj 0 2)));

    //                 let mod2 = (rec (int 0) (not (proj 0 2)));
    //                 let plus_mod2 = (maybe_increment (not (is_even (proj 0 2))) (proj 1 2));
    //                 let half = (rec (int 0) (plus_mod2 (proj 1 2) (proj 0 2)));

    //                 let hd = (half double);
    //                 let ident = (proj 0 1);
    //                 let hd_scase = (S (proj 0 2));

    //         //        let half = (rec (int 0) )
    //                 let bl = (rec Z (const 2 (int 1)));
    //                 let ed = (is_even double);
    //                 let edz = (ed (const 0 Z));
    //                 let eds = (ed (S (proj 0 1)));

    //                 let zcase = (int 1);
    //                 let scase = (not (not (proj 0 2)));
    //                 let scase_applied = (scase ed (proj 0 1));

    //                 let nn = (not not);
    //                 let nns = (nn S);

    //                 let bl = (rec Z (const 2 (int 1)));

    //                 let one = (const 1 (int 1));
    //                 let one_zcase = (int 1);
    //                 let one_scase = (const 2 (int 1));

    //                 let maybe_or_not_increment = (maybe_increment (not (proj 0 2)) (maybe_increment (proj 0 2) (proj 1 2)));
    //                 let increment_arg1 = (S (proj 1 2));
    //                 let rec_bridge = (rec S (S (proj 2 3)));

    //                 let factored = (maybe_or_not_increment (not (is_even double)) (half double));
    //             ];

    //     println!(
    //         "{:?}",
    //         Goal::new(ed.clone(), prec![(const 1 (int 1))])
    //             .unwrap()
    //             .induction(prec![((not not) (proj 0 2))])
    //             .auto()
    //             .swap()
    //             .induction(prec![((not not) (proj 0 2))])
    //             .auto()
    //             .rec()
    //             // .simplify()
    //             // .swap()
    //             // .simplify()
    //             // .swap()
    //             .auto() //            .auto()

    //                     //  .auto()
    //                     // .auto()
    //                     //            .rec()
    //                     //        .cut(prec![(rec Z )])

    //                     //           .induction(prec![((not not) (proj 0 2))])
    //                     // .auto()
    //                     // .swap()
    //                     // .induction(prec![((not not) (proj 0 2))])
    //                     // .auto()
    //                     // .auto() //        .auto()
    //                     //     .cut(factored.clone())
    //                     //     .auto()
    //                     //        .simplify()
    //     );
}

// (((int 0) * !2) * <((rec (int 1) ((int 0) * !2)) * (stack (proj 0 1) (empty 1))); (stack (proj 0 1) (empty 1))>)

// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp S (stack (proj 0 1) (empty 1)))
//         (empty 1)))

// (comp (comp Z (empty 2))
//     (stack
//         (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (stack (proj 0 1) (empty 1)) (empty 1)))
//         (stack (stack (proj 0 1) (empty 1)) (empty 1))))

// wanted to match:
// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp
//             (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//             (stack
//                 (comp S (stack (comp (comp S (stack (comp S (stack (comp S (stack (comp S (stack Z (empty 0))) (empty 0))) (empty 0))) (empty 0))) (empty 1)) (comp (empty 0) (empty 1))))
//                 (empty 1)))
//         (empty 1)))

// reduction was for:
// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp
//             (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//             (stack
//                 (comp S (stack (comp (comp S (stack (comp S (stack (comp S (stack (comp S (stack Z (empty 0))) (empty 0))) (empty 0))) (empty 0))) (empty 1)) (empty 1)))
//                 (empty 1)))
//     (empty 1)))
