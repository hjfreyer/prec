// #[derive(Debug)]
// enum Fn<'a> {
//     Z(usize),
//     S,
//     Proj(usize, usize),
//     Comp(&'a Fn<'a>, Vec<Fn<'a>>),
//     Rec(&'a Fn<'a>, &'a Fn<'a>),
// }
use im::Vector;
use std::fmt;
use std::rc::Rc;

//use typed_arena::Arena;

#[derive(Clone, Debug, PartialEq, Eq)]
enum FnEnum {
    Z(usize),
    S,
    Proj(usize, usize),
    Comp(Fn, Vector<Fn>),
    Rec(Fn, Fn),

    Alias(&'static str, Fn),
    Int(i32, usize),
}

//type Fn = Rc<FnEnum>;
#[derive(Clone, PartialEq, Eq)]
pub struct Fn(Rc<FnEnum>);

impl Fn {
    pub fn z(arity: usize) -> Fn {
        Fn(Rc::new(FnEnum::Z(arity)))
    }
    pub fn s() -> Fn {
        Fn(Rc::new(FnEnum::S))
    }
    pub fn proj(selector: usize, arity: usize) -> Fn {
        Fn(Rc::new(FnEnum::Proj(selector, arity)))
    }
    pub fn comp(f: Fn, gs: im::Vector<Fn>) -> Fn {
        Fn(Rc::new(FnEnum::Comp(f, gs)))
    }
    pub fn rec(f: Fn, g: Fn) -> Fn {
        Fn(Rc::new(FnEnum::Rec(f, g)))
    }
    pub fn alias(name: &'static str, f: Fn) -> Fn {
        Fn(Rc::new(FnEnum::Alias(name, f)))
    }
    pub fn int(value: i32, arity: usize) -> Fn {
        Fn(Rc::new(FnEnum::Int(value, arity)))
    }
}

impl fmt::Debug for Fn {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &*self.0 {
            FnEnum::Z(a) => f.write_fmt(format_args!("Z_{}", a)),
            //            FnEnum::Z(_) => f.write_str("Z"),
            FnEnum::S => f.write_str("S"),
            FnEnum::Proj(select, _) => f.write_fmt(format_args!("P[{}]", select)),
            FnEnum::Rec(fr, g) => f.write_fmt(format_args!("Rec[{:?}, {:?}]", fr, g)),
            FnEnum::Comp(fun, gs) => {
                f.write_str("(")?;

                f.write_fmt(format_args!("{:?}", fun))?;
                for g in gs {
                    f.write_str(" ")?;
                    f.write_fmt(format_args!("{:?}", g))?;
                }

                f.write_str(")")
            }
            FnEnum::Alias(name, _) => f.write_str(name),
            FnEnum::Int(value, arity) => f.write_fmt(format_args!("(int {} {})", value, arity)),
        }
    }
}

// struct Arena<'a> {
//     fns: Vec<Fn<'a>>
// }

// impl<'a> Arena<'a> {
//     fn take(&mut self, f: Fn<'a>) {
//         self.fns.push(f)
//     }

//     fn z(&mut self, arity: usize)-> &'a Fn<'a> {
//         self.fns.push(Fn::Z(arity));
//         return &self.fns[self.fns.len() - 1]
//     }
// }

#[derive(Debug)]
enum BadFn {
    Bad,
}

fn arity(Fn(f): &Fn) -> Result<usize, BadFn> {
    match &**f {
        &FnEnum::Z(n) => Ok(n),
        &FnEnum::S => Ok(1),
        &FnEnum::Proj(idx, of) => {
            if idx < of {
                Ok(of)
            } else {
                Err(BadFn::Bad)
            }
        }
        FnEnum::Comp(f, gs) => {
            if arity(f)? != gs.len() || gs.len() == 0 {
                Err(BadFn::Bad)
            } else {
                let first_arity = arity(&gs[0])?;
                for g in gs {
                    if arity(g)? != first_arity {
                        return Err(BadFn::Bad);
                    }
                }
                Ok(first_arity)
            }
        }
        FnEnum::Rec(f, g) => {
            let f_arity = arity(f)?;
            if f_arity + 2 != arity(g)? {
                Err(BadFn::Bad)
            } else {
                Ok(f_arity + 1)
            }
        }
        FnEnum::Alias(_, f) => arity(f),
        &FnEnum::Int(_, arity) => Ok(arity),
    }
}

#[derive(Debug)]
enum Reduction {
    Redux(Fn),
    AlreadyReduced(Fn),
}

// macro_rules! reduction_rule {
//     ((Z $arity:ident)) => {Fn::z($arity)};
//     (@fn S) => {Fn::s()};
//     (@fn (int $value:tt $arity:tt)) => {Fn::int($value, $arity)};
//     (@fn (true $arity:tt)) => {Fn::int(1, $arity)};
//     (@fn (false $arity:tt)) => {Fn::int(0, $arity)};
//     (@fn (rec $f:tt $g:tt)) => {
//         Fn::rec(prec![@fn $f], prec![@fn $g])
//     };
//     (@fn (raw $v:expr)) => {$v};
//     (@fn (proj $select:tt $arity:tt)) => {
//         Fn::proj($select, $arity)
//     };
//     (@fn ($f:tt $($gs:tt)+)) => {
//         Fn::comp(prec![@fn $f], vec![$(prec![@fn $gs]),+].into())
//     };
//     (@fn $f:ident) => {$f};
//     ($(let $name:ident = $fun:tt;)*) => {
//         $(
//             let $name = Fn::alias(stringify!($name), prec!(@fn $fun));
//         )*
//     };
// }

fn reduce_fully(f: &Fn) -> Result<Fn, BadFn> {
    let mut expr = f.clone();
    println!("{:?}", expr);
    while let Reduction::Redux(nx) = reduce(&expr)? {
        expr = nx;
        println!("{:?}", expr);
    }
    expr = resolve_fully(&expr)?;
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
    if let Some(r) = reduce_rec_zero(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_rec_succ(func)? {
        return Ok(Some(r));
    }
    if let Some(r) = reduce_rec_succ2(func)? {
        return Ok(Some(r));
    }

    if let FnEnum::Comp(f, gs) = &*func.0 {
        if let Some(r) = reduce_with_preference(f)? {
            return Ok(Some(Fn::comp(r, gs.clone())));
        }

        let mut i = gs.iter();
        let mut new_g = im::vector![];
        let mut any_reduced = false;
        while let Some(g) = i.next() {
            if let Some(r) = reduce_with_preference(g)? {
                new_g.push_back(r);
                any_reduced = true;
            } else {
                new_g.push_back(g.clone())
            }
        }
        if any_reduced {
            while let Some(g) = i.next() {
                new_g.push_back(g.clone())
            }
            return Ok(Some(Fn::comp(f.clone(), new_g)));
        }
    }

    Ok(None)
}

// match &*f.0 {
//     &FnEnum::Z(_) | &FnEnum::S | &FnEnum::Proj(_, _) | &FnEnum::Rec(_, _) => {
//         Ok(Reduction::AlreadyReduced(f.clone()))
//     }
//     FnEnum::Alias(_, fun) => return Ok(Reduction::Redux(fun.clone())),
//     &FnEnum::Int(value, arity) => {
//         if value == 0 {
//             Ok(Reduction::Redux(Fn::z(arity)))
//         } else {
//             Ok(Reduction::Redux(Fn::comp(
//                 Fn::s(),
//                 im::vector![Fn::int(value - 1, arity)],
//             )))
//         }
//     }
//     FnEnum::Comp(cf, cgs) => {
//         match &*cf.0 {
//             &FnEnum::Z(_) => {
//                 let new_arity = arity(&cgs[0])?;
//                 return Ok(Reduction::Redux(Fn::z(new_arity)));
//             }
//             &FnEnum::S => (),
//             &FnEnum::Proj(select, _) => return Ok(Reduction::Redux(cgs[select].clone())),
//             FnEnum::Alias(_, _) => (),
//             FnEnum::Int(_, _) => (),

//             FnEnum::Comp(int_f, int_gs) => {
//                 let new_gs = int_gs
//                     .iter()
//                     .map(|g| Fn::comp(g.clone(), cgs.clone()))
//                     .collect();
//                 return Ok(Reduction::Redux(Fn::comp(int_f.clone(), new_gs)));
//             }

//             // Handled below.
//             FnEnum::Rec(_, _) => {}
//         };

//         if let Reduction::Redux(redux) = reduce(&cf)? {
//             return Ok(Reduction::Redux(Fn::comp(redux, cgs.clone())));
//         }

//         let mut any_reduced = false;
//         let mut ngs = vec![];
//         for g in cgs.iter().map(reduce) {
//             match g? {
//                 Reduction::Redux(redux) => {
//                     any_reduced = true;
//                     ngs.push(redux);
//                 }
//                 Reduction::AlreadyReduced(orig) => {
//                     ngs.push(orig);
//                 }
//             }
//         }
//         if any_reduced {
//             return Ok(Reduction::Redux(Fn::comp(cf.clone(), ngs.into())));
//         }

//         //
//         Ok(Reduction::AlreadyReduced(f.clone()))
//     }
// }

// fn get_redex(f: &Fn) -> Result<Vec<Fn>, BadFn> {
// let mut ranked : Vec<(i32, f)>= vec![];

// fn rec(f: &Fn) {

// }
//     //
// }
fn resolve(func: &Fn) -> Result<Fn, BadFn> {
    match &*func.0 {
        FnEnum::Alias(_, f) => resolve(f),
        &FnEnum::Int(value, arity) => {
            if value == 0 {
                Ok(Fn::z(arity))
            } else {
                Ok(Fn::comp(Fn::s(), im::vector![Fn::int(value - 1, arity)]))
            }
        }

        FnEnum::Z(_) | FnEnum::S | FnEnum::Proj(_, _) | FnEnum::Rec(_, _) | FnEnum::Comp(_, _) => {
            Ok(func.clone())
        }
    }
}

fn resolve_fully(func: &Fn) -> Result<Fn, BadFn> {
    match &*func.0 {
        FnEnum::Alias(_, f) => resolve_fully(f),
        &FnEnum::Int(value, arity) => Ok(intf(value, arity)),
        FnEnum::Rec(f, g) => Ok(Fn::rec(resolve_fully(f)?, resolve_fully(g)?)),

        FnEnum::Comp(f, gs) => {
            let new_gs: Result<im::Vector<Fn>, BadFn> = gs.iter().map(resolve_fully).collect();
            Ok(Fn::comp(resolve_fully(&f)?, new_gs?))
        }
        FnEnum::Z(_) | FnEnum::S | FnEnum::Proj(_, _) => Ok(func.clone()),
    }
}

// fn reduce_int(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let &FnEnum::Int(value, arity) = &*func.0 {
//         if 0 < value {
//             Ok(Some(Fn::comp(
//                 Fn::s(),
//                 im::vector![Fn::int(value - 1, arity)],
//             )))
//         } else {
//             Ok(Some(Fn::z(arity)))
//         }
//     } else {
//         Ok(None)
//     }
// }

// fn reduce_alias(func: &Fn) -> Result<Option<Fn>, BadFn> {
//     if let FnEnum::Alias(name, func) = &*func.0 {
//         Ok(Some(func.clone()))
//     } else {
//         Ok(None)
//     }
// }

fn reduce_z_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let FnEnum::Z(_) = &*resolve(f)?.0 {
            let any_arg = gs.head().ok_or(BadFn::Bad)?;
            return Ok(Some(Fn::z(arity(any_arg)?)));
        }
    };
    Ok(None)
}

fn reduce_proj_elim(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let &FnEnum::Proj(select, _) = &*resolve(f)?.0 {
            let arg = gs.get(select).ok_or(BadFn::Bad)?;
            return Ok(Some(arg.clone()));
        }
    };
    Ok(None)
}

fn reduce_comp_distribute(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let FnEnum::Comp(int_f, int_gs) = &*resolve(f)?.0 {
            let new_gs = int_gs
                .iter()
                .map(|g| Fn::comp(g.clone(), gs.clone()))
                .collect();
            return Ok(Some(Fn::comp(int_f.clone(), new_gs)));
        }
    }
    Ok(None)
}

// Reduces statement Pr[f, g] * (Z, ...a) =>
//     f * (...a)
fn reduce_rec_zero(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let FnEnum::Rec(z_case, _) = &*resolve(f)?.0 {
            let first_arg = gs.head().ok_or(BadFn::Bad)?;
            if let FnEnum::Z(_) = &*resolve(first_arg)?.0 {
                let a = gs.skip(1);
                if a.is_empty() {
                    return Ok(Some(z_case.clone()));
                } else {
                    return Ok(Some(Fn::comp(z_case.clone(), a)));
                }
            }
        }
    }

    Ok(None)
}

// fn reduce_nullary_comp(fun: &Fn) -> Reduction {
//     if let FnEnum::Comp(func, args) = &*fun.0 {

// }

// Reduces statement Pr[f, g] * (S * a, ...b) =>
//     g * (Pr[f, g] * (a, ...b), a, ...b)
fn reduce_rec_succ(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let FnEnum::Rec(_, s_case) = &*resolve(f)?.0 {
            let first_arg = gs.head().ok_or(BadFn::Bad)?;
            let b = gs.skip(1);

            if let FnEnum::Comp(maybe_s, maybe_singleton_a) = &*resolve(first_arg)?.0 {
                if let FnEnum::S = &*resolve(maybe_s)?.0 {
                    let a = maybe_singleton_a.head().ok_or(BadFn::Bad)?;

                    let decremented_args = im::vector![a.clone()] + b.clone();
                    let rec_call = Fn::comp(f.clone(), decremented_args.clone());
                    return Ok(Some(Fn::comp(
                        s_case.clone(),
                        im::vector![rec_call] + decremented_args,
                    )));
                }
            }
        }
    }
    Ok(None)
}

// Reduces statement Pr[f, g] * (S, ...b) =>
//     g * (Pr[f, g] * (P[0], ...b), P[0], ...b)
fn reduce_rec_succ2(func: &Fn) -> Result<Option<Fn>, BadFn> {
    if let FnEnum::Comp(f, gs) = &*resolve(func)?.0 {
        if let FnEnum::Rec(_, s_case) = &*resolve(f)?.0 {
            let first_arg = gs.head().ok_or(BadFn::Bad)?;
            let b = gs.skip(1);

            if let FnEnum::S = &*resolve(first_arg)?.0 {
                let decremented_args = im::vector![Fn::proj(0, 1)] + b.clone();
                let rec_call = Fn::comp(f.clone(), decremented_args.clone());
                return Ok(Some(Fn::comp(
                    s_case.clone(),
                    im::vector![rec_call] + decremented_args,
                )));
            }
        }
    }
    Ok(None)
}

// fn reduce_vec(gs : &Vector<Fn>) -> Result<(Vector<Fn>, bool), ReductionErr> {
//     let res : Vec<Fn> = vec![];

//     for (i, g )in gs.iter().map(reduce).enumerate() {
//         match g()
//     }

//     Ok((res.into(), true))
// }

fn intf(i: i32, arity: usize) -> Fn {
    let mut res: Fn = Fn(Rc::new(FnEnum::Z(arity)));
    for _ii in 0..i {
        res = Fn::comp(Fn::s(), im::vector![res]);
    }
    res
}

fn eq_after_reduction(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
    Ok(reduce_fully(f)? == reduce_fully(g)?)
}

// fn intf<'a>(i : i32, arity: usize)-> Fn<'a> {
//     let mut res = Fn::Z(arity);
//     for _ii in 0..i {
//         res = Fn::Comp(Fn::S, vec![res])
//     }
//     res
// }

// const a :Arena<Fn>= Arena::new<Fn>();

// macro_rules! comp {
//     ($fn:expr, $($arg:expr),*) => {

//     }
// }

macro_rules! prec {
    (@fn (Z $arity:tt)) => {Fn::z($arity)};
    (@fn S) => {Fn::s()};
    (@fn (int $value:tt $arity:tt)) => {Fn::int($value, $arity)};
    (@fn (true $arity:tt)) => {Fn::int(1, $arity)};
    (@fn (false $arity:tt)) => {Fn::int(0, $arity)};
    (@fn (rec $f:tt $g:tt)) => {
        Fn::rec(prec![@fn $f], prec![@fn $g])
    };
    (@fn (raw $v:expr)) => {$v};
    (@fn (proj $select:tt $arity:tt)) => {
        Fn::proj($select, $arity)
    };
    (@fn ($f:tt $($gs:tt)+)) => {
        Fn::comp(prec![@fn $f], vec![$(prec![@fn $gs]),+].into())
    };
    (@fn $f:ident) => {$f.clone()};
    ($(let $name:ident = $fun:tt;)*) => {
        $(
            let $name = Fn::alias(stringify!($name), prec!(@fn $fun));
        )*
    };
}
//trace_macros!(true);

fn check_zero_eq(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
    eq_after_reduction(
        &Fn::comp(f.clone(), im::vector![Fn::z(0)]),
        &Fn::comp(g.clone(), im::vector![Fn::z(0)]),
    )
}

fn check_succ_eq(f: &Fn, g: &Fn) -> Result<bool, BadFn> {
    eq_after_reduction(
        &Fn::comp(f.clone(), im::vector![Fn::s()]),
        &Fn::comp(g.clone(), im::vector![Fn::s()]),
    )
}

fn main() {
    prec![
        let t = (int 1 0);
        let not = (rec t (false 2));
        let is_even = (rec (true 0) (not (proj 0 2)));

        let double = (rec (int 0 0) (S (S (proj 0 2))));
        let bl = (rec (Z 0) (int 1 2));
        let x = (not not);
    ];
    let mut expr = x;

    println!("{:?}", check_succ_eq(&expr, &bl));
    println!("{:?}", resolve_fully(&t));
    arity(&expr).unwrap();
    //expr = reduce_fully(&expr).unwrap()
}
