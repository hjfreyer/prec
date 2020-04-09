#![feature(box_syntax, box_patterns, label_break_value, bindings_after_at)]
#![allow(dead_code)]

//use im::Vector;
use std::fmt;

#[derive(Clone, PartialEq, Eq)]
struct FnMeta {
    alias: Option<&'static str>,
    int: Option<i32>,
}

impl FnMeta {
    const NONE: FnMeta = FnMeta {
        alias: None,
        int: None,
    };
}

#[derive(Clone, PartialEq, Eq)]
enum Fn {
    Z(FnMeta),
    S(FnMeta),
    Proj(usize, usize, FnMeta),
    Comp(Box<Fn>, FnMatrix, FnMeta),
    Rec(Box<Fn>, Box<Fn>, FnMeta),
}

#[derive(Clone, PartialEq, Eq)]
enum FnMatrix {
    Empty(usize),
    Cons(Box<Fn>, Box<FnMatrix>),
}

impl FnMatrix {
    fn len(&self) -> usize {
        return self.into_iter().count();
    }

    fn new(arity: usize, fns: &[Fn]) -> FnMatrix {
        if fns.is_empty() {
            FnMatrix::Empty(arity)
        } else {
            FnMatrix::Cons(box fns[0].clone(), box FnMatrix::new(arity, &fns[1..]))
        }
    }

    fn new_nonconst(fns: &[Fn]) -> Result<FnMatrix, BadFn> {
        let head = fns.get(0).ok_or(BadFn::Bad)?;
        Ok(FnMatrix::new(arity(head)?, fns))
    }

    fn map<F: ::std::ops::Fn(&Fn) -> Fn>(&self, arity: usize, mapper: F) -> FnMatrix {
        match self {
            FnMatrix::Empty(_) => FnMatrix::Empty(arity),
            FnMatrix::Cons(box f, box cdr) => {
                FnMatrix::Cons(box mapper(f), box cdr.map(arity, mapper))
            }
        }
    }

    fn eye(arity: usize) -> Self {
        let mut res = FnMatrix::Empty(arity);
        for i in (0..arity).rev() {
            res = FnMatrix::Cons(box Fn::Proj(i, arity, FnMeta::NONE), box res)
        }
        res
    }

    fn apply_to_index<E, F: ::std::ops::Fn(&Fn) -> Result<Fn, E>>(
        &self,
        index: usize,
        mapper: F,
    ) -> Option<Self> {
        match (index, self) {
            (0, FnMatrix::Cons(box car, cdr)) => {
                Some(FnMatrix::Cons(box mapper(car).ok()?, cdr.clone()))
            }
            (n, FnMatrix::Cons(box car, box cdr)) => Some(FnMatrix::Cons(
                box car.clone(),
                box cdr.apply_to_index(n - 1, mapper)?,
            )),
            (_, FnMatrix::Empty(_)) => None,
        }
    }
}

impl<'a> IntoIterator for &'a FnMatrix {
    type Item = &'a Box<Fn>;
    type IntoIter = FnMatrixIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        FnMatrixIterator(self)
    }
}

#[derive(Clone)]
struct FnMatrixIterator<'a>(&'a FnMatrix);

impl<'a> Iterator for FnMatrixIterator<'a> {
    type Item = &'a Box<Fn>;
    fn next(&mut self) -> Option<&'a Box<Fn>> {
        let (res, new) = match self {
            FnMatrixIterator(FnMatrix::Empty(_)) => (None, None),
            FnMatrixIterator(FnMatrix::Cons(f, box cdr)) => (Some(f), Some(FnMatrixIterator(cdr))),
        };
        if let Some(iter) = new {
            *self = iter;
        }
        res
    }
}

fn set_meta(func: Fn, meta: FnMeta) -> Fn {
    match func {
        Fn::Z(_) => Fn::Z(meta),
        Fn::S(_) => Fn::S(meta),
        Fn::Proj(select, arity, _) => Fn::Proj(select, arity, meta),
        Fn::Comp(f, gs, _) => Fn::Comp(f, gs, meta),
        Fn::Rec(f, g, _) => Fn::Rec(f, g, meta),
    }
}

#[derive(Debug)]
enum BadFn {
    Bad,
}

fn arity(f: &Fn) -> Result<usize, BadFn> {
    match f {
        Fn::Z(_) => Ok(0),
        Fn::S(_) => Ok(1),
        &Fn::Proj(select, arity, _) => {
            if select < arity {
                Ok(arity)
            } else {
                Err(BadFn::Bad)
            }
        }
        Fn::Comp(box f, gs, _) => {
            if arity(&f)? == gs.len() {
                matrix_arity(gs)
            } else {
                Err(BadFn::Bad)
            }
        }
        Fn::Rec(f, g, _) => {
            let f_arity = arity(&*f)?;
            if f_arity + 2 != arity(&*g)? {
                Err(BadFn::Bad)
            } else {
                Ok(f_arity + 1)
            }
        }
    }
}

fn matrix_arity(m: &FnMatrix) -> Result<usize, BadFn> {
    match m {
        FnMatrix::Empty(arity) => Ok(*arity),
        FnMatrix::Cons(box f, box cdr) => {
            let f_arity = arity(f)?;
            let cdr_arity = matrix_arity(cdr)?;
            if f_arity == cdr_arity {
                Ok(f_arity)
            } else {
                Err(BadFn::Bad)
            }
        }
    }
}

impl Fn {
    pub fn z() -> Fn {
        Fn::Z(FnMeta::NONE)
    }
    pub fn s() -> Fn {
        Fn::S(FnMeta::NONE)
    }
    pub fn proj(selector: usize, arity: usize) -> Fn {
        Fn::Proj(selector, arity, FnMeta::NONE)
    }
    // Panics if gs is empty.
    pub fn comp(f: Fn, gs: &[Fn]) -> Fn {
        Fn::Comp(box f, FnMatrix::new_nonconst(gs).unwrap(), FnMeta::NONE)
    }
    pub fn mk_const(arity: usize, f: Fn) -> Fn {
        Fn::Comp(box f, FnMatrix::Empty(arity), FnMeta::NONE)
    }
    pub fn rec(f: Fn, g: Fn) -> Fn {
        Fn::Rec(box f, box g, FnMeta::NONE)
    }
    pub fn alias(name: &'static str, f: Fn) -> Fn {
        set_meta(
            f,
            FnMeta {
                alias: Some(name),
                int: None,
            },
        )
    }
    pub fn int(value: i32) -> Fn {
        let mut res: Fn = Fn::Z(FnMeta {
            alias: None,
            int: Some(0),
        });
        for ii in 0..value {
            res = Fn::Comp(
                box Fn::S(FnMeta::NONE),
                FnMatrix::new(0, &[res]),
                FnMeta {
                    alias: None,
                    int: Some(ii + 1),
                },
            );
        }
        res
    }
}

const UNPACK_META: bool = false;

impl fmt::Debug for Fn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn meta_or<F>(f: &mut fmt::Formatter<'_>, meta: &FnMeta, els: F) -> fmt::Result
        where
            F: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
        {
            if UNPACK_META {
                els(f)
            } else {
                match meta {
                    FnMeta {
                        alias: Some(name),
                        int: _,
                    } => f.write_str(name),
                    FnMeta {
                        alias: None,
                        int: Some(value),
                    } => f.write_fmt(format_args!("{}", value)),
                    FnMeta {
                        alias: None,
                        int: None,
                    } => els(f),
                }
            }
        }
        match &self {
            Fn::Z(meta) => meta_or(f, meta, |f| f.write_str("Z")),
            Fn::S(meta) => meta_or(f, meta, |f| f.write_str("S")),
            Fn::Proj(select, _, meta) => {
                meta_or(f, meta, |f| f.write_fmt(format_args!("P[{}]", select)))
            }
            Fn::Rec(fr, g, meta) => meta_or(f, meta, |f| {
                f.write_fmt(format_args!("Rec[{:?}, {:?}]", fr, g))
            }),
            Fn::Comp(box fun, FnMatrix::Empty(arity), meta) => meta_or(f, meta, |f| {
                f.write_fmt(format_args!("(const {} {:?})", arity, fun))
            }),
            Fn::Comp(box fun, gs, meta) => meta_or(f, meta, |f| {
                f.write_str("(")?;

                f.write_fmt(format_args!("{:?}", fun))?;
                for g in gs {
                    f.write_str(" ")?;
                    f.write_fmt(format_args!("{:?}", g))?;
                }

                f.write_str(")")
            }),
        }
    }
}

macro_rules! prec {
    (@fn Z) => {Fn::z()};
    (@fn S) => {Fn::s()};
    (@fn (int $value:tt)) => {Fn::int($value)};
    (@fn (rec $f:tt $g:tt)) => {
        Fn::rec(prec![@fn $f], prec![@fn $g])
    };
    (@fn (raw $v:expr)) => {$v};
    (@fn (proj $select:tt $arity:tt)) => {
        Fn::proj($select, $arity)
    };
    (@fn (const $arity:tt $f:tt)) => {
        Fn::mk_const($arity, prec![@fn $f])
    };
    (@fn ($f:tt $($gs:tt)+)) => {
        Fn::comp(prec![@fn $f], &[$(prec![@fn $gs]),+])
    };
    (@fn $f:ident) => {$f.clone()};
    ($(let $name:ident = $fun:tt;)*) => {
        $(
            let $name = Fn::alias(stringify!($name), prec!(@fn $fun));
        )*
    };
}

#[derive(Clone, Debug)]
enum Path {
    // Generic.
    Identity,
    Composition(Box<Path>, Box<Path>),

    // Projection
    ProjElimSelect,
    ProjElimSkip,

    // Composition.
    CompDistribute,
    CompLeft(Box<Path>),
    CompRight(usize, Box<Path>),
    EtaAbstraction(usize),
    EtaReduction(usize),

    // Recursion.
    RecElimZ,
    RecElimS,
}

#[derive(Debug)]
enum RewriteErr {
    BadFn(BadFn),
    MisappliedRule(Path),
}

fn rewrite(func: &Fn, rule: &Path) -> Result<Fn, RewriteErr> {
    match (rule, func) {
        (
            Path::ProjElimSelect,
            Fn::Comp(box Fn::Proj(0, _, _), FnMatrix::Cons(box car, _), _),
        ) => Ok(car.clone()),

        (
            Path::ProjElimSkip,
            Fn::Comp(box Fn::Proj(select, arity, _), FnMatrix::Cons(_, box cdr), _),
        ) if 0 < *select => Ok(Fn::Comp(
            box Fn::Proj(*select - 1, *arity - 1, FnMeta::NONE),
            cdr.clone(),
            FnMeta::NONE,
        )),

        // (Path::ZElim, Fn::Comp(box z @ Fn::Z(_), FnMatrix::Cons(_, box cdr), _)) => {
        //     Ok(Fn::Comp(box z.clone(), cdr.clone(), FnMeta::NONE))
        // }

        (
            Path::CompDistribute,
            Fn::Comp(box Fn::Comp(box int_f, int_gs, FnMeta { int: None, .. }), ext_gs, _),
        ) => {
            let new_gs = int_gs.map(matrix_arity(ext_gs).map_err(RewriteErr::BadFn)?, |g| {
                Fn::Comp(box g.clone(), ext_gs.clone(), FnMeta::NONE)
            });
            Ok(Fn::Comp(box int_f.clone(), new_gs, FnMeta::NONE))
        }

        // Reduces statement Pr[z_case, s_case] * (Z * (), ...b) =>
        //     z_case * (...b)
        (
            Path::RecElimZ,
            Fn::Comp(
                box Fn::Rec(z_case, _, _),
                FnMatrix::Cons(box Fn::Comp(box Fn::Z(_), FnMatrix::Empty(_), _), box b),
                _,
            ),
        ) => Ok(Fn::Comp(z_case.clone(), b.clone(), FnMeta::NONE)),

        // Reduces statement Pr[z_case, s_case] * (S * a, ...b) =>
        //     s_case * (Pr[z_case, s_case] * (a, ...b), a, ...b)
        (
            Path::RecElimS,
            Fn::Comp(
                rec @ box Fn::Rec(_, s_case, _),
                FnMatrix::Cons(
                    box Fn::Comp(box Fn::S(_), FnMatrix::Cons(a, box FnMatrix::Empty(_)), _),
                    b,
                ),
                _,
            ),
        ) => {
            let decremented_args = FnMatrix::Cons(a.clone(), b.clone());
            let rec_call = Fn::Comp(rec.clone(), decremented_args.clone(), FnMeta::NONE);
            Ok(Fn::Comp(
                s_case.clone(),
                FnMatrix::Cons(box rec_call, box decremented_args),
                FnMeta::NONE,
            ))
        }

        (Path::EtaAbstraction(arity), f) => {
            Ok(Fn::Comp(box f.clone(), FnMatrix::eye(*arity), FnMeta::NONE))
        }

        (Path::CompLeft(box rec_rule), Fn::Comp(f, gs, _)) => Ok(Fn::Comp(
            box rewrite(f, rec_rule)?,
            gs.clone(),
            FnMeta::NONE,
        )),

        (Path::CompRight(index, box rec_rule), Fn::Comp(f, gs, _)) => Ok(Fn::Comp(
            f.clone(),
            gs.apply_to_index(*index, |g| rewrite(g, rec_rule))
                .ok_or(RewriteErr::MisappliedRule(rule.clone()))?,
            FnMeta::NONE,
        )),

        (Path::EtaReduction(arity), Fn::Comp(box f, gs, _))
            if *gs == FnMatrix::eye(*arity) =>
        {
            Ok(f.clone())
        }

        _ => Err(RewriteErr::MisappliedRule(rule.clone())),
    }
}

// fn rewrite_proj_elim_select(func: &Fn) -> Result<Fn, RewriteErr> {
//     match func {
//         => Ok(car.clone()),
//         _ => Err(RewriteErr::MisappliedRule(Path::ProjElimSelect)),
//     }
// }

// fn rewrite_proj_elim_skip(func: &Fn) -> Result<Fn, RewriteErr> {
//     match func {
//         Fn::Comp(box Fn::Proj(n, _, _), FnMatrix::Cons(_, box cdr), _) if 0 < *n => {
//             Ok(Fn::Comp(box Fn::Proj(n, _, _), FnMatrix::Cons(_, box cdr), _))},
//         _ => Err(RewriteErr::MisappliedRule(Path::ProjElimSelect)),
//     }
// }

#[derive(Debug)]
enum Reduction {
    Redux(Fn),
    AlreadyReduced(Fn),
}

fn reduce_fully(f: &Fn) -> Result<Fn, BadFn> {
    let mut expr = f.clone();
    println!("{:?}", expr);
    while let Reduction::Redux(nx) = reduce(&expr)? {
        expr = nx;
        println!("{:?}", expr);
    }
    println!("reduced: {:?}", expr);
    Ok(expr)
}

fn reduce(f: &Fn) -> Result<Reduction, BadFn> {
    if let Some(rr) = suggest_rewrite(f)? {
        return Ok(Reduction::Redux(rewrite(f, &rr).expect("something wrong with reduction")));
    }
    Ok(Reduction::AlreadyReduced(f.clone()))
}

fn suggest_rewrite(f: &Fn) -> Result<Option<Path>, BadFn> {
    macro_rules! try_rewrite {
        ($rule:expr) => {
            match rewrite(f, &$rule) {
                Ok(f) => return Ok(Some($rule)),
                Err(RewriteErr::MisappliedRule(_)) => (),
                Err(RewriteErr::BadFn(b)) => return Err(b),
            }
        };
    }
    try_rewrite![Path::ProjElimSelect];
    try_rewrite![Path::ProjElimSkip];
//    try_rewrite![Path::ZElim];
    let arity = arity(f)?;

    try_rewrite![Path::EtaReduction(arity)];
    try_rewrite![Path::CompDistribute];
    try_rewrite![Path::RecElimZ];
    try_rewrite![Path::RecElimS];

    if let Fn::Comp(box Fn::Rec(_, _, _), FnMatrix::Cons(box Fn::Z(_), _), _) = f {
        try_rewrite![Path::CompRight(
            0,
            box Path::EtaAbstraction(0)
        )];
    }
    if let Fn::Comp(box Fn::Rec(_, _, _), FnMatrix::Cons(box Fn::S(_), _), _) = f {
        try_rewrite![Path::CompRight(
            0,
            box Path::EtaAbstraction(1)
        )];
    }

    if let Fn::Comp(box f, gs, _) = f {
        if let Some(rr) = suggest_rewrite(f)? {
            return Ok(Some(Path::CompLeft(box rr)));
        }
        for (idx, g) in gs.into_iter().enumerate() {
            if let Some(rr) = suggest_rewrite(g)? {
                return Ok(Some(Path::CompRight(idx, box rr)));
            }
        }
    }

    Ok(None)
}

// fn reduce_with_preference(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Some(r) = reduce_z_elim(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_proj_elim(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_comp_distribute(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_const_undistribute(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_rec_zero(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_rec_succ(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_rec_succ2(func)? {
//         return Ok(Some(r));
//     }
//     if let Some(r) = reduce_const_elim(func)? {
//         return Ok(Some(r));
//     }

//     if let Fn::Comp(box f, g_arity, gs, _) = func {
//         if let Some(r) = reduce_with_preference(f)? {
//             return Ok(Some(Fn::Comp(box r, *g_arity, gs.clone(), FnMeta::NONE)));
//         }

//         let mut i = gs.iter();
//         let mut new_g = im::vector![];
//         let mut any_reduced = false;
//         while let Some(box g) = i.next() {
//             if let Some(r) = reduce_with_preference(g)? {
//                 new_g.push_back(box r);
//                 any_reduced = true;
//             } else {
//                 new_g.push_back(box g.clone())
//             }
//         }
//         if any_reduced {
//             while let Some(g) = i.next() {
//                 new_g.push_back(g.clone())
//             }
//             return Ok(Some(Fn::Comp(box f.clone(), *g_arity, new_g, FnMeta::NONE)));
//         }
//     }

//     Ok(None)
// }

// fn reduce_z_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box Fn::Z(_), 0, _, _) = func {
//         return Ok(Some(Fn::z()));
//     };
//     Ok(None)
// }

// fn reduce_proj_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box Fn::Proj(select, _, _), g_arity, gs, _) = func {
//         let box arg = gs.get(*select).ok_or(BadFn::Bad)?;
//         return Ok(Some(arg.clone()));
//     };
//     Ok(None)
// }

// fn reduce_comp_distribute(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box Fn::Comp(int_f, _, int_gs, _), g_arity, gs, _) = func {
//         if gs.is_empty() {
//             return Ok(None);
//         }
//         let new_gs = int_gs
//             .iter()
//             .map(|g| box Fn::Comp(g.clone(), *g_arity, gs.clone(), FnMeta::NONE))
//             .collect();
//         return Ok(Some(Fn::Comp(
//             int_f.clone(),
//             *g_arity,
//             new_gs,
//             FnMeta::NONE,
//         )));
//     }
//     Ok(None)
// }

// fn reduce_const_undistribute(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box f, g_arity, gs, _) = func {
//         if gs.is_empty() {
//             return Ok(None);
//         }
//         fn deconst(g: &Box<Fn>) -> Option<Box<Fn>> {
//             if let box Fn::Comp(box int_f, int_arity, int_gs, _) = g {
//                 if int_gs.is_empty() {
//                     return Some(box int_f.clone());
//                 }
//             };
//             None
//         }
//         let deconsted: Option<im::Vector<Box<Fn>>> = gs.iter().map(deconst).collect();
//         if let Some(new_gs) = deconsted {
//             return Ok(Some(Fn::Comp(
//                 box Fn::Comp(box f.clone(), 0, new_gs, FnMeta::NONE),
//                 *g_arity,
//                 im::vector![],
//                 FnMeta::NONE,
//             )));
//         }
//     }
//     Ok(None)
// }

// fn reduce_const_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box f, 0, gs, _) = func {
//         if gs.is_empty() {
//             return Ok(Some(f.clone()));
//         }
//     }
//     Ok(None)
// }

// // Reduces statement Pr[f, g] * (Z, ...a) =>
// //     f * (...a)
// fn reduce_rec_zero(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box f @ Fn::Rec(box z_case, _, _), g_arity, gs, _) = func {
//         let first_arg = gs.head().ok_or(BadFn::Bad)?;
//         if let box Fn::Z(_) = first_arg {
//             let a = gs.skip(1);
//             return Ok(Some(Fn::Comp(
//                 box z_case.clone(),
//                 *g_arity,
//                 a,
//                 FnMeta::NONE,
//             )));
//         }
//     }

//     Ok(None)
// }

// // Reduces statement Pr[f, g] * (S * a, ...b) =>
// //     g * (Pr[f, g] * (a, ...b), a, ...b)
// fn reduce_rec_succ(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box f @ Fn::Rec(_, box s_case, _), orig_arity, gs, _) = func {
//         let first_arg = gs.head().ok_or(BadFn::Bad)?;
//         let b = gs.skip(1);

//         if let box Fn::Comp(box Fn::S(_), arg_arity, maybe_singleton_a, _) = first_arg {
//             let a = maybe_singleton_a.head().ok_or(BadFn::Bad)?;

//             let decremented_args = im::vector![a.clone()] + b.clone();
//             let rec_call = Fn::Comp(
//                 box f.clone(),
//                 *orig_arity,
//                 decremented_args.clone(),
//                 FnMeta::NONE,
//             );
//             return Ok(Some(Fn::Comp(
//                 box s_case.clone(),
//                 *orig_arity,
//                 im::vector![box rec_call] + decremented_args,
//                 FnMeta::NONE,
//             )));
//         }
//     }
//     Ok(None)
// }

// // Reduces statement Pr[f, g] * (S, ...b) =>
// //     g * (Pr[f, g] * (P[0], ...b), P[0], ...b)
// fn reduce_rec_succ2(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let Fn::Comp(box f @ Fn::Rec(_, s_case, _), g_arity, gs, _) = func {
//         let first_arg = gs.head().ok_or(BadFn::Bad)?;
//         let b = gs.skip(1);

//         if let box Fn::S(_) = first_arg {
//             // Assert that g_arity = 1, as would be implied by the S.
//             if *g_arity != 1 {
//                 return Err(BadFn::Bad);
//             }
//             let decremented_args = im::vector![box Fn::proj(0, 1)] + b;
//             let rec_call = Fn::Comp(
//                 box f.clone(),
//                 *g_arity,
//                 decremented_args.clone(),
//                 FnMeta::NONE,
//             );
//             return Ok(Some(Fn::Comp(
//                 s_case.clone(),
//                 *g_arity,
//                 im::vector![box rec_call] + decremented_args,
//                 FnMeta::NONE,
//             )));
//         }
//     }
//     Ok(None)
// }

// fn intf(i: i32) -> Fn {
//     let mut res: Fn = Fn::Z(FnMeta {
//         alias: None,
//         int: Some(0),
//     });
//     for ii in 0..i {
//         res = Fn::Comp(
//             box Fn::S(FnMeta::NONE),
//             0,
//             im::vector![box res],
//             FnMeta {
//                 alias: None,
//                 int: Some(ii + 1),
//             },
//         );
//     }
//     res
// }

// // Compares h to Pr[f, g] by comparing how they operate on Z.
// fn check_pr_z(h: &Fn, f: &Fn, g: &Fn) -> Result<bool, BadFn> {
//     let prec = Fn::rec(f.clone(), g.clone());

//     Ok(reduce_fully(&Fn::comp(prec, im::vector![box Fn::z()]))?
//         == reduce_fully(&Fn::comp(h.clone(), im::vector![box Fn::z()]))?)
// }

// fn check_pr_s(h: &Fn, f: &Fn, g: &Fn) -> Result<bool, BadFn> {
//     Ok(reduce_fully(&Fn::comp(
//         g.clone(),
//         im::vector![box h.clone(), box Fn::proj(0, 1)],
//     ))? == reduce_fully(&Fn::comp(h.clone(), im::vector![box Fn::s()]))?)
// }

fn main() {
    prec![
        let a = ((proj 2 3) (int 0) (int 1) (int 2));
        let t1 = (Z (int 0) (int 1) (int 2));
        let t2 = (Z (const 2 (int 0)) (const 2 (int 1)) (const 2 (int 2)));
        let t3 = (((proj 0 2) (proj 1 3) (proj 0 3)) (int 0) (int 1) (int 2));
        let not = (rec (int 1) (const 2 Z));

        let t4 = (not Z);
        let t5 = (not S);
        let t6 = (not (const 5 Z));

        let is_even = (rec (int 1) (not (proj 0 2)));

        let double = (rec (int 0) (S (S (proj 0 2))));
        let bl = (rec Z (const 2 (int 1)));
        let x = ((is_even double) S);
        let y = ((not not) (proj 0 2));
    ];
    // let mut expr = x;
    // println!("{:?}", check_pr_s(&expr, &Fn::int(1), &y))
    // prec!

    // println!("{:?}", check_succ_eq(&expr, &bl));
    // println!("{:?}", resolve_fully(&t));
    // arity(&expr).unwrap();
    // expr = reduce_fully(&expr).unwrap()
    reduce_fully(&x).unwrap();
    //    println!("{:?}", reduce_fully(&rewrite(&t4, &Path::CompRight(0, box Path::EtaAbstraction(0))).unwrap()).unwrap());
}
