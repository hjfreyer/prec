#![feature(box_syntax, box_patterns, label_break_value, bindings_after_at)]
#![allow(dead_code, unused_variables)]

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

#[derive(Clone)]
enum Fn {
    Z(FnMeta),
    S(FnMeta),
    Proj(usize, usize, FnMeta),
    Comp(Box<Fn>, FnMatrix, FnMeta),
    Rec(Box<Fn>, Box<Fn>, FnMeta),
}

#[derive(Debug)]
enum BadFn {
    SelectOutOfBounds(Fn),
    ArityMismatch(Fn),
    MatrixArityMismatch(FnMatrix),
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
        let head = gs.get(0).expect("Empty slice passed to Fn::comp");
        let head_arity = head.arity().expect("Invalid function passed to helper.");
        Fn::Comp(box f, FnMatrix::new(head_arity, gs), FnMeta::NONE)
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

    fn arity(&self) -> Result<usize, BadFn> {
        match self {
            Fn::Z(_) => Ok(0),
            Fn::S(_) => Ok(1),
            &Fn::Proj(select, arity, _) => {
                if select < arity {
                    Ok(arity)
                } else {
                    Err(BadFn::SelectOutOfBounds(self.clone()))
                }
            }
            Fn::Comp(box f, gs, _) => {
                if f.arity()? == gs.len() {
                    gs.arity()
                } else {
                    Err(BadFn::ArityMismatch(self.clone()))
                }
            }
            Fn::Rec(box f, box g, _) => {
                let f_arity = f.arity()?;
                if f_arity + 2 != g.arity()? {
                    Err(BadFn::ArityMismatch(self.clone()))
                } else {
                    Ok(f_arity + 1)
                }
            }
        }
    }

    fn syntax_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Fn::Z(_), Fn::Z(_)) => true,
            (Fn::Z(_), _) => false,
            (Fn::S(_), Fn::S(_)) => true,
            (Fn::S(_), _) => false,
            (Fn::Proj(s_select, s_arity, _), Fn::Proj(o_select, o_arity, _)) => {
                s_select == o_select && s_arity == o_arity
            }
            (Fn::Proj(_, _, _), _) => false,
            (Fn::Comp(box s_f, s_gs, _), Fn::Comp(box o_f, o_gs, _)) => {
                s_f.syntax_eq(o_f) && s_gs.syntax_eq(o_gs)
            }
            (Fn::Comp(_, _, _), _) => false,
            (Fn::Rec(box s_f, s_g, _), Fn::Rec(box o_f, o_g, _)) => {
                s_f.syntax_eq(o_f) && s_g.syntax_eq(o_g)
            }
            (Fn::Rec(_, _, _), _) => false,
        }
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

    fn get(&self, idx: usize) -> Option<&Fn> {
        match self {
            FnMatrix::Empty(_) => None,
            FnMatrix::Cons(box car, _) if idx == 0 => Some(car),
            FnMatrix::Cons(_, box cdr) => cdr.get(idx - 1),
        }
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

    fn z(arity: usize) -> Self {
        let z = Fn::mk_const(arity - 1, Fn::z());
        let eye = FnMatrix::eye(arity - 1);
        FnMatrix::Cons(box z, box eye)
    }

    fn s(arity: usize) -> Self {
        let s = Fn::comp(Fn::s(), &[Fn::proj(0, arity)]);
        let mut eye = FnMatrix::Empty(arity);
        for i in (1..arity).rev() {
            eye = FnMatrix::Cons(box Fn::proj(i, arity), box eye)
        }
        FnMatrix::Cons(box s, box eye)
    }

    fn arity(&self) -> Result<usize, BadFn> {
        match self {
            FnMatrix::Empty(arity) => Ok(*arity),
            FnMatrix::Cons(box f, box cdr) => {
                let f_arity = f.arity()?;
                let cdr_arity = cdr.arity()?;
                if f_arity == cdr_arity {
                    Ok(f_arity)
                } else {
                    Err(BadFn::MatrixArityMismatch(self.clone()))
                }
            }
        }
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

    fn replace(&self, index: usize, f: Fn) -> Option<Self> {
        match (index, self) {
            (0, FnMatrix::Cons(box car, cdr)) => Some(FnMatrix::Cons(box f, cdr.clone())),
            (n, FnMatrix::Cons(box car, box cdr)) => {
                Some(FnMatrix::Cons(box car.clone(), box cdr.replace(n - 1, f)?))
            }
            (_, FnMatrix::Empty(_)) => None,
        }
    }

    fn syntax_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (FnMatrix::Empty(s_arity), FnMatrix::Empty(o_arity)) => s_arity == o_arity,
            (FnMatrix::Empty(_), _) => false,
            (
                FnMatrix::Cons(box self_car, box self_cdr),
                FnMatrix::Cons(box other_car, box other_cdr),
            ) => self_car.syntax_eq(other_car) && self_cdr.syntax_eq(other_cdr),
            (FnMatrix::Cons(_, _), _) => false,
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

#[derive(Copy, Clone, Debug)]
enum Step {
    // Projection
    ProjElim,

    // Composition.
    CompDistribute,
    EtaAbstraction,
    EtaReduction,

    // Recursion.
    RecElimZ,
    RecElimS,
}

#[derive(Clone, Debug)]
enum Path {
    Identity(Fn),
    Step(Fn, Step, Fn),
    Dot(Box<Path>, Box<Path>),
    Inverse(Box<Path>),
    CompLeft(Fn, Box<Path>, Fn),
    CompRight(Fn, usize, Box<Path>, Fn),

    Induction(Fn, Box<Path>, Box<Path>, Fn),
}

impl Path {
    fn start(&self) -> &Fn {
        match self {
            Path::Identity(f) => f,
            Path::Step(start, _, _) => start,
            Path::Dot(l, _) => l.start(),
            Path::CompLeft(start, _, _) => start,
            Path::CompRight(start, _, _, _) => start,
            Path::Induction(start, _, _, _) => start,
            Path::Inverse(box p) => p.end(),
        }
    }

    fn end(&self) -> &Fn {
        match self {
            Path::Identity(f) => f,
            Path::Step(_, _, end) => end,
            Path::Dot(_, r) => r.end(),
            Path::CompLeft(_, _, end) => end,
            Path::CompRight(_, _, _, end) => end,
            Path::Induction(_, _, _, end) => end,
            Path::Inverse(box p) => p.start(),
        }
    }

    fn step(func: &Fn, st: Step) -> Result<Path, RewriteErr> {
        match (st, func) {
            (
                Step::ProjElim,
                Fn::Comp(box Fn::Proj(select, arity, _), FnMatrix::Cons(box car, box cdr), _),
            ) => {
                if *select == 0 {
                    Ok(Path::Step(func.clone(), st, car.clone()))
                } else {
                    Ok(Path::Step(
                        func.clone(),
                        st,
                        Fn::Comp(
                            box Fn::Proj(*select - 1, *arity - 1, FnMeta::NONE),
                            cdr.clone(),
                            FnMeta::NONE,
                        ),
                    ))
                }
            }
            (Step::ProjElim, _) => Err(RewriteErr::MisappliedRule(st)),

            (Step::CompDistribute, Fn::Comp(box Fn::Comp(box int_f, int_gs, _), ext_gs, _)) => {
                let new_gs = int_gs.map(ext_gs.arity().map_err(RewriteErr::BadFn)?, |g| {
                    Fn::Comp(box g.clone(), ext_gs.clone(), FnMeta::NONE)
                });
                Ok(Path::Step(
                    func.clone(),
                    st,
                    Fn::Comp(box int_f.clone(), new_gs, FnMeta::NONE),
                ))
            }
            (Step::CompDistribute, _) => Err(RewriteErr::MisappliedRule(st)),

            // Reduces statement Pr[z_case, s_case] * (Z * (), ...b) =>
            //     z_case * (...b)
            (
                Step::RecElimZ,
                Fn::Comp(
                    box Fn::Rec(z_case, _, _),
                    FnMatrix::Cons(box Fn::Comp(box Fn::Z(_), FnMatrix::Empty(_), _), box b),
                    _,
                ),
            ) => Ok(Path::Step(
                func.clone(),
                st,
                Fn::Comp(z_case.clone(), b.clone(), FnMeta::NONE),
            )),
            (Step::RecElimZ, _) => Err(RewriteErr::MisappliedRule(st)),

            // Reduces statement Pr[z_case, s_case] * (S * a, ...b) =>
            //     s_case * (Pr[z_case, s_case] * (a, ...b), a, ...b)
            (
                Step::RecElimS,
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
                Ok(Path::Step(
                    func.clone(),
                    st,
                    Fn::Comp(
                        s_case.clone(),
                        FnMatrix::Cons(box rec_call, box decremented_args),
                        FnMeta::NONE,
                    ),
                ))
            }
            (Step::RecElimS, _) => Err(RewriteErr::MisappliedRule(st)),

            (Step::EtaAbstraction, f) => {
                let arity = f.arity().map_err(RewriteErr::BadFn)?;
                Ok(Path::Step(
                    func.clone(),
                    st,
                    Fn::Comp(box f.clone(), FnMatrix::eye(arity), FnMeta::NONE),
                ))
            }

            (Step::EtaReduction, Fn::Comp(box f, gs, _))
                if gs.syntax_eq(&FnMatrix::eye(gs.len())) =>
            {
                println!("ETA: {:?} {:?}", f, gs);
                Ok(Path::Step(func.clone(), st, f.clone()))
            }
            (Step::EtaReduction, _) => Err(RewriteErr::MisappliedRule(st)),
        }
    }

    fn dot(l: &Path, r: &Path) -> Result<Path, RewriteErr> {
        if l.end().syntax_eq(r.start()) {
            Ok(Path::Dot(box l.clone(), box r.clone()))
        } else {
            Err(RewriteErr::IncompatiblePaths(l.clone(), r.clone()))
        }
    }

    fn comp_left(func: &Fn, p: &Path) -> Result<Path, RewriteErr> {
        if let Fn::Comp(box f, gs, _) = func {
            if p.start().syntax_eq(f) {
                return Ok(Path::CompLeft(
                    func.clone(),
                    box p.clone(),
                    Fn::Comp(box p.end().clone(), gs.clone(), FnMeta::NONE),
                ));
            }
        }
        Err(RewriteErr::IncompatibleFunctionAndPath(
            func.clone(),
            p.clone(),
        ))
    }

    fn comp_right(func: &Fn, idx: usize, p: &Path) -> Result<Path, RewriteErr> {
        let mk_err = || RewriteErr::IncompatibleFunctionAndPath(func.clone(), p.clone());
        if let Fn::Comp(f, gs, _) = func {
            let at_idx = gs.get(idx).ok_or_else(mk_err)?;

            if at_idx.syntax_eq(p.start()) {
                return Ok(Path::CompRight(
                    func.clone(),
                    idx,
                    box p.clone(),
                    Fn::Comp(
                        f.clone(),
                        gs.replace(idx, p.end().clone())
                            .expect("We just checked that at_idx is in bounds"),
                        FnMeta::NONE,
                    ),
                ));
            }
        }

        return Err(mk_err());
    }

    fn induction(
        func: &Fn,
        z_case: &Fn,
        s_case: &Fn,
        z_path: &Path,
        s_path: &Path,
    ) -> Result<Path, RewriteErr> {
        let func_arity = func.arity().map_err(RewriteErr::BadFn)?;

        let func_z_start = Fn::Comp(box func.clone(), FnMatrix::z(func_arity), FnMeta::NONE);
        if !z_path.start().syntax_eq(&func_z_start) {
            return Err(RewriteErr::InductionZPathStartIncorrect(
                func_z_start,
                z_path.start().clone(),
            ));
        }
        if !z_path.end().syntax_eq(z_case) {
            return Err(RewriteErr::InductionZPathEndIncorrect(
                z_case.clone(),
                z_path.end().clone(),
            ));
        }

        let func_s_start = Fn::Comp(box func.clone(), FnMatrix::s(func_arity), FnMeta::NONE);
        let s_path_applied = Fn::Comp(
            box s_case.clone(),
            FnMatrix::Cons(box func.clone(), box FnMatrix::eye(func_arity)),
            FnMeta::NONE,
        );
        if !s_path.start().syntax_eq(&func_s_start) {
            return Err(RewriteErr::InductionSPathStartIncorrect(
                func_s_start,
                s_path.start().clone(),
            ));
        }

        if !s_path.end().syntax_eq(&s_path_applied) {
            return Err(RewriteErr::InductionSPathEndIncorrect(
                s_path_applied,
                s_path.end().clone(),
            ));
        }
        Ok(Path::Induction(
            func.clone(),
            box z_path.clone(),
            box s_path.clone(),
            Fn::rec(z_case.clone(), s_case.clone()),
        ))
    }

    // fn factor_constant(func: &Fn, st: Step) -> Result<Path, RewriteErr> {
    //     if let Fn::Comp(box f, )
    // }
}

#[derive(Debug)]
enum RewriteErr {
    BadFn(BadFn),
    MisappliedRule(Step),
    IncompatiblePaths(Path, Path),
    IncompatibleFunctionAndPath(Fn, Path),
    InductionZPathStartIncorrect(Fn, Fn),
    InductionSPathStartIncorrect(Fn, Fn),
    InductionZPathEndIncorrect(Fn, Fn),
    InductionSPathEndIncorrect(Fn, Fn),
}

fn reduce_fully(f: &Fn) -> Result<Path, BadFn> {
    let mut path = Path::Identity(f.clone());
    println!("{:?}", path.end());
    while let Some(ext) = suggest_extension(path.end())? {
        println!("{:?}", ext);

        path = Path::dot(&path, &ext).map_err(|e| match e {
            RewriteErr::BadFn(b) => b,
            _ => panic!("bad"),
        })?;
        println!("{:?}", path.end());
    }
    println!("reduced");
    Ok(path)
}

fn suggest_extension(func: &Fn) -> Result<Option<Path>, BadFn> {
    macro_rules! try_step {
        ($rule:expr) => {
            match Path::step(func, $rule) {
                Ok(p) => return Ok(Some(p)),
                Err(RewriteErr::BadFn(b)) => return Err(b),
                Err(_) => (),
            }
        };
    }
    try_step![Step::ProjElim];
    try_step![Step::EtaReduction];
    try_step![Step::CompDistribute];
    try_step![Step::RecElimZ];
    try_step![Step::RecElimS];

    if let Fn::Comp(box Fn::Rec(_, _, _), FnMatrix::Cons(box arg0 @ Fn::Z(_), _), _) = func {
        let z_path = Path::step(arg0, Step::EtaAbstraction).expect("EtaAbstraction always works");
        return Ok(Some(
            Path::comp_right(func, 0, &z_path).expect("EtaAbstraction always works"),
        ));
    }
    if let Fn::Comp(box Fn::Rec(_, _, _), FnMatrix::Cons(box arg0 @ Fn::S(_), _), _) = func {
        let s_path = Path::step(arg0, Step::EtaAbstraction).expect("EtaAbstraction always works");
        return Ok(Some(
            Path::comp_right(func, 0, &s_path).expect("EtaAbstraction always works"),
        ));
    }

    if let Fn::Comp(box f, gs, _) = func {
        if let Some(ext) = suggest_extension(f)? {
            return Ok(Some(Path::comp_left(func, &ext).expect("bad suggestion")));
        }
        for (idx, g) in gs.into_iter().enumerate() {
            if let Some(ext) = suggest_extension(g)? {
                return Ok(Some(
                    Path::comp_right(func, idx, &ext).expect("bad suggestion"),
                ));
            }
        }
    }

    Ok(None)
}

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

fn run_test(func: &Fn) {
    func.arity().unwrap();
    reduce_fully(func).unwrap();
}

fn find_path(start: &Fn, end: &Fn) -> Result<Option<Path>, BadFn> {
    println!("Start: {:?}; Destination: {:?}", start, end);
    let start_reduced = reduce_fully(start)?;
    let end_reduced = reduce_fully(end)?;
    if start_reduced.end().syntax_eq(end_reduced.end()) {
        Ok(Some(
            Path::dot(&start_reduced, &Path::Inverse(box end_reduced)).unwrap(),
        ))
    } else {
        Ok(None)
    }
}

fn find_induction(start: &Fn, z_case: &Fn, s_case: &Fn) -> Result<Option<Path>, BadFn> {
    let start_arity = start.arity()?;
    let z_app = Fn::Comp(box start.clone(), FnMatrix::z(start_arity), FnMeta::NONE);
    let s_app = Fn::Comp(box start.clone(), FnMatrix::s(start_arity), FnMeta::NONE);

    let s_case_unrolled = Fn::Comp(
        box s_case.clone(),
        FnMatrix::Cons(box start.clone(), box FnMatrix::eye(start_arity)),
        FnMeta::NONE,
    );

    let z_path = find_path(&z_app, z_case)?;
    let s_path = find_path(&s_app, &s_case_unrolled)?;

    if let (Some(z_path), Some(s_path)) = (z_path, s_path) {
        Path::induction(start, z_case, s_case, &z_path, &s_path)
            .map(|p| Some(p))
            .map_err(|e| match e {
                RewriteErr::BadFn(b) => b,
                _ => panic!("{:?}", e),
            })
    } else {
        Ok(None)
    }
}

fn find_path_via(start: &Fn, end: &Fn, s_case: &Fn) -> Result<Option<Path>, BadFn> {
    let z_case = &Fn::Comp(box start.clone(), FnMatrix::z(start.arity()?), FnMeta::NONE);
    let start_pr_path = find_induction(start, z_case, s_case)?;
    let end_pr_path = find_induction(end, z_case, s_case)?;
    if let (Some(start_pr_path), Some(end_pr_path)) = (start_pr_path, end_pr_path) {
        Ok(Some(
            Path::dot(&start_pr_path, &Path::Inverse(box end_pr_path)).unwrap(),
        ))
    } else {
        Ok(None)
    }
}

fn main() {
    prec![
            let a = ((proj 2 3) (int 0) (int 1) (int 2));
            let t1 = ((const 3 Z) (int 0) (int 1) (int 2));
            let t2 = ((const 3 Z) (const 2 (int 0)) (const 2 (int 1)) (const 2 (int 2)));
            let t3 = (((proj 0 2) (proj 1 3) (proj 0 3)) (int 0) (int 1) (int 2));
            let not = (rec (int 1) (const 2 Z));

            let t4 = (not Z);
            let t5 = (not S);
            let t6 = (not (const 5 Z));
            let t7 = (not (not (const 1 (int 5))));

            let is_even = (rec (int 1) (not (proj 0 2)));

            let double = (rec (int 0) (S (S (proj 0 2))));
            let mod2 = (rec (int 0) (not (proj 0 2)));
    //        let half = (rec (int 0) )
            let bl = (rec Z (const 2 (int 1)));
            let ed = (is_even double);
            let edz = (ed (const 0 Z));
            let eds = (ed (S (proj 0 1)));

            let zcase = (int 1);
            let scase = (not (not (proj 0 2)));
            let scase_applied = (scase ed (proj 0 1));

            let nn = (not not);
            let nns = (nn S);

            let one = (const 1 (int 1));
            let one_zcase = (int 1);
            let one_scase = (const 2 (int 1));
        ];
    // let mut expr = x;
    // println!("{:?}", check_pr_s(&expr, &Fn::int(1), &y))
    // prec!

    // println!("{:?}", check_succ_eq(&expr, &bl));
    // println!("{:?}", resolve_fully(&t));
    // arity(&expr).unwrap();
    // expr = reduce_fully(&expr).unwrap()
    //   let zpath = find_path(&edz, &zcase).unwrap().unwrap();
    // let spath = find_path(&eds, &scase_applied).unwrap().unwrap();

    //println!("{:?}", find_induction(&one, &zcase, &scase));

    //println!("{:?}", find_path_via(&ed, &one, &scase));
    reduce_fully(&nns);
    // run_test(&t7)
    //    println!("{:?}", reduce_fully(&rewrite(&t4, &Step::CompRight(0, box Step::EtaAbstraction(0))).unwrap()).unwrap());
}
