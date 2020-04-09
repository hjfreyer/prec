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
    CompLeft(Fn, Box<Path>, Fn),
    CompRight(Fn, usize, Box<Path>, Fn),
}

impl Path {
    fn start(&self) -> &Fn {
        match self {
            Path::Identity(f) => f,
            Path::Step(start, _, _) => start,
            Path::Dot(l, _) => l.start(),
            Path::CompLeft(start, _, _) => start,
            Path::CompRight(start, _, _, _) => start,
        }
    }

    fn end(&self) -> &Fn {
        match self {
            Path::Identity(f) => f,
            Path::Step(_, _, end) => end,
            Path::Dot(_, r) => r.end(),
            Path::CompLeft(_, _, end) => end,
            Path::CompRight(_, _, _, end) => end,
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

            (
                Step::CompDistribute,
                Fn::Comp(box Fn::Comp(box int_f, int_gs, FnMeta { int: None, .. }), ext_gs, _),
            ) => {
                let new_gs = int_gs.map(matrix_arity(ext_gs).map_err(RewriteErr::BadFn)?, |g| {
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
                let arity = arity(f).map_err(RewriteErr::BadFn)?;
                Ok(Path::Step(
                    func.clone(),
                    st,
                    Fn::Comp(box f.clone(), FnMatrix::eye(arity), FnMeta::NONE),
                ))
            }

            (Step::EtaReduction, Fn::Comp(box f, gs, _)) if *gs == FnMatrix::eye(gs.len()) => {
                Ok(Path::Step(func.clone(), st, f.clone()))
            }
            (Step::EtaReduction, _) => Err(RewriteErr::MisappliedRule(st)),
        }
    }

    fn dot(l: &Path, r: &Path) -> Result<Path, RewriteErr> {
        if l.end() == r.start() {
            Ok(Path::Dot(box l.clone(), box r.clone()))
        } else {
            Err(RewriteErr::IncompatiblePaths(l.clone(), r.clone()))
        }
    }

    fn comp_left(func: &Fn, p: &Path) -> Result<Path, RewriteErr> {
        if let Fn::Comp(box f, gs, _) = func {
            if p.start() == f {
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

            if at_idx == p.start() {
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
}

#[derive(Debug)]
enum RewriteErr {
    BadFn(BadFn),
    MisappliedRule(Step),
    IncompatiblePaths(Path, Path),
    IncompatibleFunctionAndPath(Fn, Path),
}

fn reduce_fully(f: &Fn) -> Result<Path, BadFn> {
    let mut path = Path::Identity(f.clone());
    println!("{:?}", path.end());
    while let Some(ext) = suggest_extension(path.end())? {
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
    arity(func).unwrap();
    reduce_fully(func).unwrap();
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
    run_test(&x)
    //    println!("{:?}", reduce_fully(&rewrite(&t4, &Step::CompRight(0, box Step::EtaAbstraction(0))).unwrap()).unwrap());
}
