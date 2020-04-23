use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use func::View as FView;
use func::{BadFunc, Func};
use im::Vector;
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Rewrite {
    view: Rc<View>,
    lhs_tag: func::Tag,
}

#[derive(Clone, Debug)]
pub enum View {
    Reverse(Rewrite),

    // Projection
    ProjCar(Func, Func),
    ProjCdr(u32, Func, Func),

    // Composition.
    CompAssoc(Func, Func, Func),
    CompDistributeEmpty(Func),
    CompDistributeStack(Func, Func, Func),

    // Eta.
    EtaReductionLeft(Func),
    EtaReductionRight(Func),

    // Recursion.
    RecElimZ(Func, Func, Func, Func),
    RecElimS(Func, Func, func::Tag, Func, Func, Func),

    // Steps in nested structures.
    CompLeft(Rewrite, Func),
    CompRight(Func, Rewrite),
    StackCar(Rewrite, Func),
    StackCdr(Func, Rewrite),
    RecZ(Rewrite, Func),
    RecS(Func, Rewrite),
}

enum Side {
    Left,
    Right,
}

impl Rewrite {
    fn new(view: View, lhs_tag: func::Tag) -> Rewrite {
        Rewrite {
            view: Rc::new(view),
            lhs_tag,
        }
    }

    fn try_side(&self, side: Side) -> Result<Func, BadFunc> {
        match (*self.view).clone() {
            // Projection.
            View::ProjCar(stack_car, stack_cdr) => match side {
                Side::Left => {
                    let select_arity = stack_cdr.arity().out + 1;
                    Func::comp(
                        Func::proj(0, select_arity)?,
                        Func::stack(stack_car, stack_cdr)?,
                    )
                }
                Side::Right => Ok(stack_car),
            },
            View::ProjCdr(select, stack_car, stack_cdr) => match side {
                Side::Left => {
                    let arity = stack_cdr.arity().out + 1;
                    Func::comp(
                        Func::proj(select, arity)?,
                        Func::stack(stack_car, stack_cdr)?,
                    )
                }
                Side::Right => {
                    let arity = stack_cdr.arity().out + 1;
                    Func::comp(Func::proj(select - 1, arity - 1)?, stack_cdr)
                }
            },

            // Composition.
            View::CompAssoc(f, g, h) => match side {
                Side::Left => Ok(Func::comp(Func::comp(f, g)?, h)?),
                Side::Right => Ok(Func::comp(f, Func::comp(g, h)?)?),
            },
            View::CompDistributeEmpty(g) => match side {
                Side::Left => Ok(Func::comp(Func::empty(g.arity().out), g)?),
                Side::Right => Ok(Func::empty(g.arity().r#in)),
            },
            View::CompDistributeStack(stack_car, stack_cdr, g) => match side {
                Side::Left => Ok(Func::comp(Func::stack(stack_car, stack_cdr)?, g)?),
                Side::Right => Ok(Func::stack(
                    Func::comp(stack_car, g.clone())?,
                    Func::comp(stack_cdr, g)?,
                )?),
            },

            // Eta.
            View::EtaReductionLeft(g) => match side {
                Side::Left => {
                    let eye = Func::eye(g.arity().out);
                    Ok(Func::comp(eye, g)?)
                }
                Side::Right => Ok(g),
            },
            View::EtaReductionRight(f) => match side {
                Side::Left => {
                    let eye = Func::eye(f.arity().r#in);
                    Ok(Func::comp(f, eye)?)
                }
                Side::Right => Ok(f),
            },

            // Recursion.
            View::RecElimZ(z_case, s_case, z_args, other_args) => match side {
                Side::Left => Ok(Func::comp(
                    Func::rec(z_case, s_case)?,
                    Func::stack(Func::comp(Func::z(), z_args)?, other_args)?,
                )?),
                Side::Right => Ok(Func::comp(z_case, other_args)?),
            },
            View::RecElimS(z_case, s_case, rec_tag, s_args_car, s_args_cdr, other_args) => {
                match side {
                    Side::Left => Ok(Func::comp(
                        Func::rec(z_case, s_case)?.set_tag(rec_tag.clone()),
                        Func::stack(
                            Func::comp(Func::s(), Func::stack(s_args_car, s_args_cdr)?)?,
                            other_args,
                        )?,
                    )?),
                    Side::Right => {
                        let decremented_args = Func::stack(s_args_car, other_args)?;
                        let rec_call = Func::comp(
                            Func::rec(z_case, s_case.clone())?.set_tag(rec_tag.clone()),
                            decremented_args.clone(),
                        )?;
                        Ok(Func::comp(
                            s_case,
                            Func::stack(rec_call, decremented_args)?,
                        )?)
                    }
                }
            }

            _ => panic!("should be handled in endpoints()"),
        }
    }

    pub fn endpoints(&self) -> Endpoints<Func> {
        match &*self.view {
            View::Reverse(rw) => {
                let Endpoints(start, end) = rw.endpoints();
                return Endpoints(end, start);
            }
            View::CompLeft(f_rw, g) => {
                return Endpoints(
                    Func::comp(f_rw.endpoints().start().clone(), g.clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::comp(f_rw.endpoints().end().clone(), g.clone()).unwrap(),
                )
            }
            View::CompRight(f, g_rw) => {
                return Endpoints(
                    Func::comp(f.clone(), g_rw.endpoints().start().clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::comp(f.clone(), g_rw.endpoints().end().clone()).unwrap(),
                )
            }
            View::StackCar(car_rw, cdr) => {
                return Endpoints(
                    Func::stack(car_rw.endpoints().start().clone(), cdr.clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::stack(car_rw.endpoints().end().clone(), cdr.clone()).unwrap(),
                )
            }
            View::StackCdr(car, cdr_rw) => {
                return Endpoints(
                    Func::stack(car.clone(), cdr_rw.endpoints().start().clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::stack(car.clone(), cdr_rw.endpoints().end().clone()).unwrap(),
                )
            }
            View::RecZ(z_rw, s_case) => {
                return Endpoints(
                    Func::rec(z_rw.endpoints().start().clone(), s_case.clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::rec(z_rw.endpoints().end().clone(), s_case.clone()).unwrap(),
                )
            }
            View::RecS(z_case, s_rw) => {
                return Endpoints(
                    Func::rec(z_case.clone(), s_rw.endpoints().start().clone())
                        .unwrap()
                        .set_tag(self.lhs_tag),
                    Func::rec(z_case.clone(), s_rw.endpoints().end().clone()).unwrap(),
                )
            }
            _ => (),
        }
        let start = self
            .try_side(Side::Left)
            .expect("validated on matching")
            .set_tag(self.lhs_tag);
        let end = self.try_side(Side::Right).expect("validated on matching");
        Endpoints(start, end)
    }
}

#[derive(Clone, Debug, Copy)]
pub enum Rule {
    // Projection
    ProjCar,
    ProjCdr,

    // Composition.
    CompAssoc,
    CompDistributeEmpty,
    CompDistributeStack,

    // Eta.
    EtaReductionLeft,
    EtaReductionRight,

    // Recursion.
    RecElimZ,
    RecElimS,

    EtaAbstractBareZ,
    EtaAbstractBareS,
}

impl Rule {
    pub fn match_start(self, func: &Func) -> Option<Rewrite> {
        let view = self.match_start_view(func.clone());
        view.map(|view| Rewrite::new(view, *func.tag()))
    }

    fn match_start_view(self, func: Func) -> Option<View> {
        match self {
            Rule::ProjCar => {
                if let FView::Comp(f, g) = func.into_view() {
                    if let (FView::Proj(select, arity), FView::Stack(car, cdr)) =
                        (f.into_view(), g.into_view())
                    {
                        if select == 0 {
                            return Some(View::ProjCar(car, cdr));
                        }
                    }
                }
                None
            }
            Rule::ProjCdr => {
                if let FView::Comp(f, g) = func.clone().into_view() {
                    if let (FView::Proj(select, arity), FView::Stack(car, cdr)) =
                        (f.into_view(), g.into_view())
                    {
                        if 0 < select {
                            return Some(View::ProjCdr(select, car, cdr));
                        }
                    }
                }
                None
            }
            Rule::CompAssoc => {
                if let FView::Comp(fg, h) = func.into_view() {
                    if let FView::Comp(f, g) = fg.into_view() {
                        return Some(View::CompAssoc(f, g, h));
                    }
                }
                None
            }
            Rule::CompDistributeEmpty => {
                if let FView::Comp(stack, g) = func.into_view() {
                    if let FView::Empty(_) = stack.into_view() {
                        Some(View::CompDistributeEmpty(g))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            Rule::CompDistributeStack => {
                if let FView::Comp(stack, g) = func.into_view() {
                    if let FView::Stack(car, cdr) = stack.into_view() {
                        Some(View::CompDistributeStack(car, cdr, g))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }

            Rule::EtaReductionLeft => {
                if let FView::Comp(f, g) = func.into_view() {
                    if f.syntax_eq(&Func::eye(g.arity().out)) {
                        Some(View::EtaReductionLeft(g))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Rule::EtaReductionRight => {
                if let FView::Comp(f, g) = func.into_view() {
                    if g.syntax_eq(&Func::eye(f.arity().r#in)) {
                        Some(View::EtaReductionRight(f))
                    } else {
                        None
                    }
                } else {
                    None
                }
            }
            Rule::RecElimZ => {
                if let FView::Comp(f, g) = func.into_view() {
                    if let (FView::Rec(z_case, s_case), FView::Stack(car, other_args)) =
                        (f.view(), g.view())
                    {
                        if let FView::Comp(f, z_args) = car.view() {
                            if let FView::Z = f.view() {
                                return Some(View::RecElimZ(
                                    z_case.clone(),
                                    s_case.clone(),
                                    z_args.clone(),
                                    other_args.clone(),
                                ));
                            }
                        }
                    }
                }
                None
            }
            Rule::RecElimS => {
                if let FView::Comp(f, g) = func.into_view() {
                    let f_tag = f.tag().clone();
                    if let (FView::Rec(z_case, s_case), FView::Stack(car, other_args)) =
                        (f.view(), g.view())
                    {
                        if let FView::Comp(f, s_args) = car.view() {
                            if let (FView::S, FView::Stack(s_args_car, s_args_cdr)) =
                                (f.view(), s_args.view())
                            {
                                return Some(View::RecElimS(
                                    z_case.clone(),
                                    s_case.clone(),
                                    f_tag,
                                    s_args_car.clone(),
                                    s_args_cdr.clone(),
                                    other_args.clone(),
                                ));
                            }
                        }
                    }
                }
                None
            },
            Rule::    EtaAbstractBareZ => {
                let (f, g) = func.decompose()?;
                f.unrec()?;
                let (g_car, g_cdr) = g.unstack()?;
                if let FView::Z = g_car.view() {
                    let eta_red = Rewrite::new(View::EtaReductionRight(Func::z()), func::Tag::None);
                    let eta_abs = Rewrite::new(View::Reverse(eta_red), func::Tag::None);

                    let g_rw = Rewrite::new(View::StackCar(eta_abs, g_cdr), *g.tag());

                    Some(View::CompRight(f, g_rw))
                } else {
                    None
                }
            }
            Rule::    EtaAbstractBareS => {
                let (f, g) = func.decompose()?;
                f.unrec()?;
                let (g_car, g_cdr) = g.unstack()?;
                if let FView::S = g_car.view() {
                    let eta_red = Rewrite::new(View::EtaReductionRight(Func::s()), func::Tag::None);
                    let eta_abs = Rewrite::new(View::Reverse(eta_red), func::Tag::None);

                    let g_rw = Rewrite::new(View::StackCar(eta_abs, g_cdr), *g.tag());

                    Some(View::CompRight(f, g_rw))
                } else {
                    None
                }
            }
        }
    }
}

pub trait Tactic {
    // Note: tactics use opposite conventions for "start" and "end".
    fn apply(&self, end_func: &Func) -> Option<(Func, Vector<Rewrite>)>;
}

pub fn reduce_fully_tactic() -> impl Tactic {
    struct Impl();
    impl Tactic for Impl {
        fn apply(&self, end_func: &Func) -> Option<(Func, Vector<Rewrite>)> {
            let reduced = reduce_fully(end_func);
            let last = reduced.last()?;
            Some((last.endpoints().end().clone(), reduced))
        }
    }
    Impl()
}

// pub fn add_free_variable(func: &Func) -> Func {
//     match func.view()
// }

// pub fn factor_helper(func: &Func, factored: &Func) -> Option<Rewrite> {
//     if func.syntax_eq(factored) {
//         return None
//     }
//     match func.view() {
//         FView::Z => None,
//         FView::S => None,
//         FView::Proj(_, _) => None,
//         FView::Empty(_) => None,
//     }
// }

// (maybe_increment (not (not (is_even double))) (maybe_increment (not (is_even double)) (half double)))

// pub fn factor(factored: &Func) -> impl Tactic {

// }

// (comp
//     (rec (proj 0 1) (comp S (stack (proj 2 3) (empty 3))))
//     (stack
//         (comp
//             (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//             (stack
//                 (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//                     (stack (comp (rec
//                         (comp S (stack Z (empty 0))) (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (proj 0 2) (empty 2)))) (stack (rec Z (comp S (stack (comp S (stack (proj 0 2) (empty 2))) (empty 2)))) (empty 1))) (empty 1))) (empty 1))) (stack (comp (rec (proj 0 1) (comp S (stack (proj 2 3) (empty 3)))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (proj 0 2) (empty 2)))) (stack (rec Z (comp S (stack (comp S (stack (proj 0 2) (empty 2))) (empty 2)))) (empty 1))) (empty 1))) (stack (comp (rec Z (comp (comp (rec (proj 0 1) (comp S (stack (proj 2 3) (empty 3)))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (proj 0 2) (empty 2)))) (stack (proj 0 2) (empty 2))) (empty 2))) (stack (proj 1 2) (empty 2)))) (stack (proj 1 2) (stack (proj 0 2) (empty 2))))) (stack (rec Z (comp S (stack (comp S (stack (proj 0 2) (empty 2))) (empty 2)))) (empty 1))) (empty 1)))) (empty 1)))) -> (S (half double))

pub trait EndMatcher {
    fn match_end(&self, func: &Func) -> Option<Rewrite>;
}

pub fn comp_factor_empty(factored: &Func) -> impl EndMatcher {
    struct Impl(Func);

    impl EndMatcher for Impl {
        fn match_end(&self, func: &Func) -> Option<Rewrite> {
            let Self(factored) = self;
            let (f, g) = factored.decompose()?;
            println!("{:?}", factored);
            None
        }
    }

    Impl(factored.clone())
}

pub fn comp_factor_stack() -> impl EndMatcher {
    struct Impl();

    impl EndMatcher for Impl {
        fn match_end(&self, func: &Func) -> Option<Rewrite> {
            let (car, cdr) = func.unstack()?;
            let (car_f, car_g) = car.decompose()?;
            let (cdr_f, cdr_g) = cdr.decompose()?;

            if car_g.syntax_eq(&cdr_g) {
                Some(Rewrite::new(
                    View::CompDistributeStack(car_f, cdr_f, car_g),
                    func::Tag::None,
                ))
            } else {
                None
            }
        }
    }

    Impl()
}

// CompDistributeEmpty,
//    CompDistributeStack

pub fn reduce_once(func: &Func) -> Option<Rewrite> {
    macro_rules !try_rules {
        ($($rule:ident),*) => {
            None
            $(.or_else(|| Rule::$rule.match_start(func)))*
        }
    }

    let rw_reduction = try_rules!(
        ProjCar,
        ProjCdr,
        ProjCar,
        ProjCdr,
        RecElimZ,
        RecElimS,
        EtaAbstractBareZ,
        EtaAbstractBareS,
        EtaReductionLeft,
        EtaReductionRight,
        CompAssoc,
        CompDistributeEmpty,
        CompDistributeStack
    );
    if let Some(rw) = rw_reduction {
        return Some(rw);
    }

    if let FView::Comp(f, g) = func.view() {
        let opt = None
            .or_else(|| {
                reduce_once(f)
                    .map(|rw| Rewrite::new(View::CompLeft(rw, g.clone()), func.tag().clone()))
            })
            .or_else(|| {
                reduce_once(g)
                    .map(|rw| Rewrite::new(View::CompRight(f.clone(), rw), func.tag().clone()))
            });
        if let Some(p) = opt {
            return Some(p);
        }
    }
    if let FView::Stack(car, cdr) = func.view() {
        let opt = None
            .or_else(|| {
                reduce_once(car)
                    .map(|rw| Rewrite::new(View::StackCar(rw, cdr.clone()), func.tag().clone()))
            })
            .or_else(|| {
                reduce_once(cdr)
                    .map(|rw| Rewrite::new(View::StackCdr(car.clone(), rw), func.tag().clone()))
            });
        if let Some(p) = opt {
            return Some(p);
        }
    }
    None
}

// Returns a path starting with f and leading to a reduced form.
pub fn reduce_fully(func: &Func) -> Vector<Rewrite> {
    let mut res = Vector::new();
    let mut func = func.clone();
    // let mut res = Path::validate(View::Refl(func.clone())).unwrap();

    while let Some(rw) = reduce_once(&func) {
        func = rw.endpoints().end().clone();
        res.push_back(rw);
           }
    res
}


// (comp (rec Z (comp (comp (rec (proj 0 1) (comp S (stack (proj 2 3) (empty 3)))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (comp (rec (comp S (stack Z (empty 0))) (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (proj 0 2) (empty 2)))) (stack (proj 0 2) (empty 2))) (empty 2))) (stack (proj 1 2) (empty 2)))) (stack (proj 1 2) (stack (proj 0 2) (empty 2))))) 
// (stack (comp 
//     (rec Z (comp S (stack (comp S (stack (proj 0 2) (empty 2))) (empty 2)))) 
//        (stack Z (empty 0))) 
//     (empty 0)))
