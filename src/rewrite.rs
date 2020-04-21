use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use func::View as FView;
use func::{BadFunc, Func};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Rewrite {
    view: Rc<View>,
    lhs_tag: func::Tag,
}

#[derive(Clone, Debug)]
pub enum View {
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
                    let select_arity = stack_cdr.arity().out() + 1;
                    Func::comp(
                        Func::proj(0, select_arity)?,
                        Func::stack(stack_car, stack_cdr)?,
                    )
                }
                Side::Right => Ok(stack_car),
            },
            View::ProjCdr(select, stack_car, stack_cdr) => match side {
                Side::Left => {
                    let arity = stack_cdr.arity().out() + 1;
                    Func::comp(
                        Func::proj(select, arity)?,
                        Func::stack(stack_car, stack_cdr)?,
                    )
                }
                Side::Right => {
                    let arity = stack_cdr.arity().out() + 1;
                    Func::comp(Func::proj(select - 1, arity - 1)?, stack_cdr)
                }
            },

            // Composition.
            View::CompAssoc(f, g, h) => match side {
                Side::Left => Ok(Func::comp(Func::comp(f, g)?, h)?),
                Side::Right => Ok(Func::comp(f, Func::comp(g, h)?)?),
            },
            View::CompDistributeEmpty(g) => match side {
                Side::Left => Ok(Func::comp(Func::empty(g.arity().out()), g)?),
                Side::Right => Ok(Func::empty(g.arity().r#in())),
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
                    let eye = Func::eye(g.arity().out());
                    Ok(Func::comp(eye, g)?)
                }
                Side::Right => Ok(g),
            },
            View::EtaReductionRight(f) => match side {
                Side::Left => {
                    let eye = Func::eye(f.arity().r#in());
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
        }
    }

    pub fn endpoints(&self) -> Endpoints<Func> {
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
                    if f.syntax_eq(&Func::eye(g.arity().out())) {
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
                    if g.syntax_eq(&Func::eye(f.arity().r#in())) {
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
            }
        }
    }
}

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
                Some(Rewrite::new(View::CompDistributeStack(car_f, cdr_f, car_g), func::Tag::None))
            } else {
                None
            }
        }
    }

    Impl()
}

// CompDistributeEmpty,
//    CompDistributeStack
