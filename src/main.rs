// #[derive(Debug)]
// enum Fn<'a> {
//     Z(usize),
//     S,
//     Proj(usize, usize),
//     Comp(&'a Fn<'a>, Vec<Fn<'a>>),
//     Rec(&'a Fn<'a>, &'a Fn<'a>),
// }
#![feature(box_syntax, box_patterns, label_break_value, bindings_after_at)]
#![allow(dead_code)]

use im::Vector;
use std::collections::HashMap;

use std::fmt;
//use std::rc::Rc;

//use typed_arena::Arena;

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
    Comp(Box<Fn>, usize, Vector<Box<Fn>>, FnMeta),
    Rec(Box<Fn>, Box<Fn>, FnMeta),
}

// #[derive(Clone, PartialEq, Eq)]
// enum Fn2 {
//     Z,
//     S,
//     Proj(usize, usize),
//     Comp(Box<Fn2>, usize, Vector<Box<Fn2>>),
//     Rec(Box<Fn2>, Box<Fn2>),

//     Alias(&'static str, Box<Fn2>),
//     Int(i32),
// }

// fn compile(func: Fn2) -> Fn {
//     match func {
//         Fn2::Z => Fn::Z(FnMeta::NONE),
//         Fn2::S => Fn::S(FnMeta::NONE),
//         Fn2::Proj(select, arity) => Fn::Proj(select, arity, FnMeta::NONE),
//         Fn2::Comp(box f, g_arity, gs) => Fn::Comp(box compile(f), g_arity,
//             gs.into_iter().map(|box g| box compile(g)).collect(), FnMeta::NONE),
// Fn2::Rec(box f, box g) => Fn::Rec(box compile(f), box compile(g), FnMeta::NONE),

//         Fn2::Alias(name, box f) => set_meta(compile(f), FnMeta {alias: Some(name), int: None})
//         Fn2::Int(value) => set_meta(compile(f), FnMeta {alias: Some(name), int: None})
//     }
// }

fn set_meta(func: Fn, meta: FnMeta) -> Fn {
    match func {
        Fn::Z(_) => Fn::Z(meta),
        Fn::S(_) => Fn::S(meta),
        Fn::Proj(select, arity, _) => Fn::Proj(select, arity, meta),
        Fn::Comp(f, g_arity, gs, _) => Fn::Comp(f, g_arity, gs, meta),
        Fn::Rec(f, g, _) => Fn::Rec(f, g, meta),
    }
}
// //type Fn = Rc<Fn>;
// // #[derive(Clone, PartialEq, Eq)]
// // pub struct Fn(Rc<Fn>);

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
        Fn::Comp(box f, g_arity, gs, _) => {
            if arity(&f)? != gs.len() {
                Err(BadFn::Bad)
            } else if gs.len() == 0 {
                Ok(*g_arity)
            } else {
                for g in gs {
                    if arity(&*g)? != *g_arity {
                        return Err(BadFn::Bad);
                    }
                }
                Ok(*g_arity)
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
    pub fn comp(f: Fn, gs: im::Vector<Box<Fn>>) -> Fn {
        let head = gs.head().unwrap();

        Fn::Comp(box f, arity(head).unwrap(), gs, FnMeta::NONE)
    }
    pub fn mk_const(arity: usize, f: Fn) -> Fn {
        Fn::Comp(box f, arity, im::vector![], FnMeta::NONE)
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
        intf(value)
    }
}

impl fmt::Debug for Fn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn meta_or<F>(f: &mut fmt::Formatter<'_>, meta: &FnMeta, els: F) -> fmt::Result
        where
            F: FnOnce(&mut fmt::Formatter<'_>) -> fmt::Result,
        {
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
        match &self {
            Fn::Z(meta) => meta_or(f, meta, |f| f.write_str("Z")),
            Fn::S(meta) => meta_or(f, meta, |f| f.write_str("S")),
            Fn::Proj(select, _, meta) => {
                meta_or(f, meta, |f| f.write_fmt(format_args!("P[{}]", select)))
            }
            Fn::Rec(fr, g, meta) => meta_or(f, meta, |f| {
                f.write_fmt(format_args!("Rec[{:?}, {:?}]", fr, g))
            }),
            Fn::Comp(box fun, arity, gs, meta) => meta_or(f, meta, |f| {
                if gs.is_empty() {
                    f.write_fmt(format_args!("(const {} {:?})", arity, fun))
                } else {
                    f.write_str("(")?;

                    f.write_fmt(format_args!("{:?}", fun))?;
                    for g in gs {
                        f.write_str(" ")?;
                        f.write_fmt(format_args!("{:?}", g))?;
                    }

                    f.write_str(")")
                }
            }),
        }
    }
}

macro_rules! prec {
    (@fn Z) => {Fn::z()};
    (@fn S) => {Fn::s()};
    (@fn (int $value:tt)) => {intf($value)};
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
        Fn::comp(prec![@fn $f], vec![$(box prec![@fn $gs]),+].into())
    };
    (@fn $f:ident) => {$f.clone()};
    ($(let $name:ident = $fun:tt;)*) => {
        $(
            let $name = Fn::alias(stringify!($name), prec!(@fn $fun));
        )*
    };
}

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
    if let Some(r) = reduce_with_preference(f)? {
        Ok(Reduction::Redux(r))
    } else {
        Ok(Reduction::AlreadyReduced(f.clone()))
    }
}

fn reduce_with_preference(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Some(r) = reduce_z_elim(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_proj_elim(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_comp_distribute(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_const_undistribute(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_rec_zero(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_rec_succ(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_rec_succ2(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_const_elim(func)? {
        return Ok(Some(r));
    }

    if let Fn::Comp(box f, g_arity, gs, _) = func {
        if let Some(r) = reduce_with_preference(f)? {
            return Ok(Some(Fn::Comp(box r, *g_arity, gs.clone(), FnMeta::NONE)));
        }

        let mut i = gs.iter();
        let mut new_g = im::vector![];
        let mut any_reduced = false;
        while let Some(box g) = i.next() {
            if let Some(r) = reduce_with_preference(g)? {
                new_g.push_back(box r);
                any_reduced = true;
            } else {
                new_g.push_back(box g.clone())
            }
        }
        if any_reduced {
            while let Some(g) = i.next() {
                new_g.push_back(g.clone())
            }
            return Ok(Some(Fn::Comp(box f.clone(), *g_arity, new_g, FnMeta::NONE)));
        }
    }

    Ok(None)
}

fn reduce_z_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box Fn::Z(_), 0, _, _) = func {
        return Ok(Some(Fn::z()));
    };
    Ok(None)
}

fn reduce_proj_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box Fn::Proj(select, _, _), g_arity, gs, _) = func {
        let box arg = gs.get(*select).ok_or(BadFn::Bad)?;
        return Ok(Some(arg.clone()));
    };
    Ok(None)
}

fn reduce_comp_distribute(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box Fn::Comp(int_f, _, int_gs, _), g_arity, gs, _) = func {
        if gs.is_empty() {
            return Ok(None);
        }
        let new_gs = int_gs
            .iter()
            .map(|g| box Fn::Comp(g.clone(), *g_arity, gs.clone(), FnMeta::NONE))
            .collect();
        return Ok(Some(Fn::Comp(
            int_f.clone(),
            *g_arity,
            new_gs,
            FnMeta::NONE,
        )));
    }
    Ok(None)
}

fn reduce_const_undistribute(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box f, g_arity, gs, _) = func {
        if gs.is_empty() {
            return Ok(None);
        }
        fn deconst(g: &Box<Fn>) -> Option<Box<Fn>> {
            if let box Fn::Comp(box int_f, int_arity, int_gs, _) = g {
                if int_gs.is_empty() {
                    return Some(box int_f.clone());
                }
            };
            None
        }
        let deconsted: Option<im::Vector<Box<Fn>>> = gs.iter().map(deconst).collect();
        if let Some(new_gs) = deconsted {
            return Ok(Some(Fn::Comp(
                box Fn::Comp(box f.clone(), 0, new_gs, FnMeta::NONE),
                *g_arity,
                im::vector![],
                FnMeta::NONE,
            )));
        }

        // let new_gs = int_gs
        //     .iter()
        //     .map(|g| box Fn::Comp(g.clone(), *g_arity, gs.clone(), FnMeta::NONE))
        //     .collect();
        // return Ok(Some(Fn::Comp(int_f.clone(), *g_arity, new_gs, FnMeta::NONE)));
    }
    Ok(None)
}

fn reduce_const_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box f, 0, gs, _) = func {
        if gs.is_empty() {
            return Ok(Some(f.clone()));
        }
    }
    Ok(None)
}

// Reduces statement Pr[f, g] * (Z, ...a) =>
//     f * (...a)
fn reduce_rec_zero(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box f @ Fn::Rec(box z_case, _, _), g_arity, gs, _) = func {
        let first_arg = gs.head().ok_or(BadFn::Bad)?;
        if let box Fn::Z(_) = first_arg {
            let a = gs.skip(1);
            return Ok(Some(Fn::Comp(
                box z_case.clone(),
                *g_arity,
                a,
                FnMeta::NONE,
            )));
        }
    }

    Ok(None)
}

// Reduces statement Pr[f, g] * (S * a, ...b) =>
//     g * (Pr[f, g] * (a, ...b), a, ...b)
fn reduce_rec_succ(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box f @ Fn::Rec(_, box s_case, _), orig_arity, gs, _) = func {
        let first_arg = gs.head().ok_or(BadFn::Bad)?;
        let b = gs.skip(1);

        if let box Fn::Comp(box Fn::S(_), arg_arity, maybe_singleton_a, _) = first_arg {
            let a = maybe_singleton_a.head().ok_or(BadFn::Bad)?;

            let decremented_args = im::vector![a.clone()] + b.clone();
            let rec_call = Fn::Comp(
                box f.clone(),
                *orig_arity,
                decremented_args.clone(),
                FnMeta::NONE,
            );
            return Ok(Some(Fn::Comp(
                box s_case.clone(),
                *orig_arity,
                im::vector![box rec_call] + decremented_args,
                FnMeta::NONE,
            )));
        }
    }
    Ok(None)
}

// Reduces statement Pr[f, g] * (S, ...b) =>
//     g * (Pr[f, g] * (P[0], ...b), P[0], ...b)
fn reduce_rec_succ2(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let Fn::Comp(box f @ Fn::Rec(_, s_case, _), g_arity, gs, _) = func {
        let first_arg = gs.head().ok_or(BadFn::Bad)?;
        let b = gs.skip(1);

        if let box Fn::S(_) = first_arg {
            // Assert that g_arity = 1, as would be implied by the S.
            if *g_arity != 1 {
                return Err(BadFn::Bad);
            }
            let decremented_args = im::vector![box Fn::proj(0, 1)] + b;
            let rec_call = Fn::Comp(
                box f.clone(),
                *g_arity,
                decremented_args.clone(),
                FnMeta::NONE,
            );
            return Ok(Some(Fn::Comp(
                s_case.clone(),
                *g_arity,
                im::vector![box rec_call] + decremented_args,
                FnMeta::NONE,
            )));
        }
    }
    Ok(None)
}

fn intf(i: i32) -> Fn {
    let mut res: Fn = Fn::Z(FnMeta {
        alias: None,
        int: Some(0),
    });
    for ii in 0..i {
        res = Fn::Comp(
            box Fn::S(FnMeta::NONE),
            0,
            im::vector![box res],
            FnMeta {
                alias: None,
                int: Some(ii + 1),
            },
        );
    }
    res
}

// // fn eq_after_reduction(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
// //     Ok(reduce_fully(f)? == reduce_fully(g)?)
// // }

// //trace_macros!(true);

// // fn check_zero_eq(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
// //     eq_after_reduction(
// //         &Fn::comp(f.clone(), im::vector![Fn::z(0)]),
// //         &Fn::comp(g.clone(), im::vector![Fn::z(0)]),
// //     )
// // }

// // fn check_succ_eq(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
// //     eq_after_reduction(
// //         &Fn::comp(f.clone(), im::vector![Fn::s()]),
// //         &Fn::comp(g.clone(), im::vector![Fn::s()]),
// //     )
// // }

// Compares h to Pr[f, g] by comparing how they operate on Z.
fn check_pr_z(h: &Fn, f: &Fn, g: &Fn) -> Result<bool, BadFn> {
    let prec = Fn::rec(f.clone(), g.clone());

    Ok(reduce_fully(&Fn::comp(prec, im::vector![box Fn::z()]))?
        == reduce_fully(&Fn::comp(h.clone(), im::vector![box Fn::z()]))?)
}

fn check_pr_s(h: &Fn, f: &Fn, g: &Fn) -> Result<bool, BadFn> {
    Ok(reduce_fully(&Fn::comp(
        g.clone(),
        im::vector![box h.clone(), box Fn::proj(0, 1)],
    ))? == reduce_fully(&Fn::comp(h.clone(), im::vector![box Fn::s()]))?)
}

fn main() {
    prec![
        let not = (rec (int 1) (const 2 Z));
        let is_even = (rec (int 1) (not (proj 0 2)));

        let double = (rec (int 0) (S (S (proj 0 2))));
        let bl = (rec Z (const 2 (int 1)));
        let x = (is_even double);
        let y = ((not not) (proj 0 2));
    ];
    let mut expr = x;
    println!("{:?}", check_pr_s(&expr, &Fn::int(1), &y))
    // prec!

    // println!("{:?}", check_succ_eq(&expr, &bl));
    // println!("{:?}", resolve_fully(&t));
    // arity(&expr).unwrap();
    // expr = reduce_fully(&expr).unwrap()
}
