use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use func::View as FView;
use func::{BadFunc, Func};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Rewrite(Rc<View>, func::Tag);

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
    EtaAbstractionLeft(Func),
    EtaReductionLeft(Func),
    EtaAbstractionRight(Func),
    EtaReductionRight(Func),

    // Recursion.
    RecElimZ(Func, Func, Func, Func),
    RecElimS(Func, Func, Func, Func, Func),

    // Induction.
    Induction(Func, Func, Rewrite),

    // Steps in nested structures.
    CompLeft(Rewrite, Func),
    CompRight(Func, Rewrite),
    StackCar(Rewrite, Func),
    StackCdr(Func, Rewrite),
    RecZ(Rewrite, Func),
    RecS(Func, Rewrite),

    // Groupoid.
    Refl(Func),
    Reverse(Rewrite),
    Concat(Rewrite, Rewrite),
}

enum Side {
    Left,
    Right,
}

impl Rewrite {
    pub fn view(&self) -> &View {
        &self.0
    }

    // Deprecate this.
    pub fn into_view(self) -> View {
        self.view().clone()
    }

    pub fn validate(view: View, tag: func::Tag) -> Result<Rewrite, BadFunc> {
        let res = Rewrite(Rc::new(view), tag);
        res.clone().try_side(Side::Left)?;
        res.clone().try_side(Side::Right)?;
        Ok(res)
    }

    fn try_side(self, side: Side) -> Result<Func, BadFunc> {
        match self.into_view() {
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
            View::EtaAbstractionLeft(g) => match side {
                Side::Left => Ok(g),
                Side::Right => {
                    let eye = Func::eye(g.arity().out());
                    Ok(Func::comp(eye, g)?)
                }
            },
            View::EtaReductionLeft(g) => match side {
                Side::Left => {
                    let eye = Func::eye(g.arity().out());
                    Ok(Func::comp(eye, g)?)
                }
                Side::Right => Ok(g),
            },
            View::EtaAbstractionRight(f) => match side {
                Side::Left => Ok(f),
                Side::Right => {
                    let eye = Func::eye(f.arity().r#in());
                    Ok(Func::comp(f, eye)?)
                }
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
            View::RecElimS(z_case, s_case, s_args_car, s_args_cdr, other_args) => match side {
                Side::Left => Ok(Func::comp(
                    Func::rec(z_case, s_case)?,
                    Func::stack(
                        Func::comp(Func::s(), Func::stack(s_args_car, s_args_cdr)?)?,
                        other_args,
                    )?,
                )?),
                Side::Right => {
                    let decremented_args = Func::stack(s_args_car, other_args)?;
                    let rec_call =
                        Func::comp(Func::rec(z_case, s_case.clone())?, decremented_args.clone())?;
                    Ok(Func::comp(
                        s_case,
                        Func::stack(rec_call, decremented_args)?,
                    )?)
                }
            },

            // Induction.
            View::Induction(f, s_case, ind_path) => match side {
                Side::Left => Ok(f),
                Side::Right => {
                    let func::Arity(_, f_arity) = f.arity();

                    // Check that ind_path fits the bill.
                    let needed_lhs = Func::comp(f.clone(), Func::s_eye(f_arity))?;
                    let needed_rhs =
                        Func::comp(s_case.clone(), Func::stack(f.clone(), Func::eye(f_arity))?)?;

                    if !ind_path
                        .endpoints()
                        .syntax_eq(&Endpoints(needed_lhs, needed_rhs))
                    {
                        panic!("todo: better error")
                    }
                    Func::rec(Func::comp(f, Func::z_eye(f_arity))?, s_case)
                }
            },

            // Nested.
            View::CompLeft(rw_f, g) => Ok(Func::comp(rw_f.try_side(side)?, g)?),
            View::CompRight(f, rw_g) => Ok(Func::comp(f, rw_g.try_side(side)?)?),
            View::StackCar(rw_car, cdr) => Ok(Func::stack(rw_car.try_side(side)?, cdr)?),
            View::StackCdr(car, rw_cdr) => Ok(Func::stack(car, rw_cdr.try_side(side)?)?),
            View::RecZ(rw_z_case, s_case) => Ok(Func::rec(rw_z_case.try_side(side)?, s_case)?),
            View::RecS(z_case, rw_s_case) => Ok(Func::rec(z_case, rw_s_case.try_side(side)?)?),

            // Groupoid
            View::Refl(f) => Ok(f),
            View::Reverse(rw) => rw.try_side(match side {
                Side::Left => Side::Right,
                Side::Right => Side::Left,
            }),
            View::Concat(p1, p2) => {
                if !p1.endpoints().end().syntax_eq(p2.endpoints().start()) {
                    panic!("put an error here")
                }
                match side {
                    Side::Left => Ok(p1.lhs()),
                    Side::Right => Ok(p2.rhs()),
                }
            }
        }
    }

    pub fn lhs(self) -> Func {
        let tag = self.1.clone();
        self.try_side(Side::Left)
            .expect("validated on creation")
            .set_tag(tag)
    }

    pub fn rhs(self) -> Func {
        self.try_side(Side::Right).expect("validated on creation")
    }

    pub fn endpoints(&self) -> Endpoints<Func> {
        Endpoints(self.clone().lhs(), self.clone().rhs())
    }
}

pub mod factory {
    use crate::base::SyntaxEq;
    use crate::func;
    use crate::func::Func;
    use crate::func::View as FView;
    use crate::rewrite::{Rewrite, View};
    pub trait Factory {
        fn for_lhs(&self, func: Func) -> Option<Rewrite>;
    }

    pub struct CompAssocFwd();
    impl Factory for CompAssocFwd {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(fg, h) = func.into_view() {
                if let FView::Comp(f, g) = fg.into_view() {
//                    println!("comp: {:?} {:?} {:?}", f, g, h);
                    Some(Rewrite::validate(View::CompAssoc(f, g, h), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct CompDistributeEmpty();
    impl Factory for CompDistributeEmpty {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(stack, g) = func.into_view() {
                if let FView::Empty(_) = stack.into_view() {
                    Some(Rewrite::validate(View::CompDistributeEmpty(g), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }
    pub struct CompDistributeStack();
    impl Factory for CompDistributeStack {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(stack, g) = func.into_view() {
                if let FView::Stack(car, cdr) = stack.into_view() {
                    Some(Rewrite::validate(View::CompDistributeStack(car, cdr, g), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct Projection();
    impl Factory for Projection {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Proj(select, arity), FView::Stack(car, cdr)) =
                    (f.into_view(), g.into_view())
                {
                    if select == 0 {
                        Some(Rewrite::validate(View::ProjCar(car, cdr), tag).unwrap())
                    } else {
                        Some(Rewrite::validate(View::ProjCdr(select, car, cdr), tag).unwrap())
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct EtaReductionLeft();
    impl Factory for EtaReductionLeft {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if f.syntax_eq(&Func::eye(g.arity().out())) {
                    Some(Rewrite::validate(View::EtaReductionLeft(g), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct EtaReductionRight();
    impl Factory for EtaReductionRight {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if g.syntax_eq(&Func::eye(f.arity().r#in())) {
                    Some(Rewrite::validate(View::EtaReductionRight(f), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct RecElimZ();
    impl Factory for RecElimZ {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Rec(z_case, s_case), FView::Stack(car, other_args)) =
                    (f.view(), g.view())
                {
                    match car.view() {
                        FView::Z => {
                            let z_eta_abstract = Rewrite::validate(
                                View::EtaAbstractionRight(Func::z()),
                                func::Tag::None,
                            )
                            .unwrap();
                            let inside_stack = Rewrite::validate(
                                View::StackCar(z_eta_abstract, other_args.clone()),
                                func::Tag::None,
                            )
                            .unwrap();
                            Some(Rewrite::validate(View::CompRight(f, inside_stack), tag).unwrap())
                        }
                        FView::Comp(f, z_args) => {
                            if let FView::Z = f.view() {
                                Some(
                                    Rewrite::validate(
                                        View::RecElimZ(
                                            z_case.clone(),
                                            s_case.clone(),
                                            z_args.clone(),
                                            other_args.clone(),
                                        ),
                                        tag,
                                    )
                                    .unwrap(),
                                )
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct RecElimS();
    impl Factory for RecElimS {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Rec(z_case, s_case), FView::Stack(car, other_args)) =
                    (f.view(), g.view())
                {
                    match car.view() {
                        FView::S => {
                            let s_eta_abstract = Rewrite::validate(
                                View::EtaAbstractionRight(Func::s()),
                                func::Tag::None,
                            )
                            .unwrap();
                            let inside_stack = Rewrite::validate(
                                View::StackCar(s_eta_abstract, other_args.clone()),
                                func::Tag::None,
                            )
                            .unwrap();
                            Some(Rewrite::validate(View::CompRight(f, inside_stack), tag).unwrap())
                        }
                        FView::Comp(f, s_args) => {
                            if let (FView::S, FView::Stack(s_args_car, s_args_cdr)) =
                                (f.view(), s_args.view())
                            {
                                Some(
                                    Rewrite::validate(
                                        View::RecElimS(
                                            z_case.clone(),
                                            s_case.clone(),
                                            s_args_car.clone(),
                                            s_args_cdr.clone(),
                                            other_args.clone(),
                                        ),
                                        tag,
                                    )
                                    .unwrap(),
                                )
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct Recurse<T: Factory>(T);
    impl<T: Factory> Factory for Recurse<T> {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let Recurse(subfactory) = self;
            let tag = func.tag();
                        println!("here: {:?}", func.view());

            match func.view() {
                FView::Comp(f, g) => None
                    .or_else(|| {
                        subfactory
                            .for_lhs(f.clone())
                            .map(|rw_f| View::CompLeft(rw_f, g.clone()))
                    })
                    .or_else(|| {
                        subfactory
                            .for_lhs(g.clone())
                            .map(|rw_g| View::CompRight(f.clone(), rw_g))
                    }),
                FView::Stack(car, cdr) => None
                    .or_else(|| {
                        subfactory
                            .for_lhs(car.clone())
                            .map(|rw_car| View::StackCar(rw_car, cdr.clone()))
                    })
                    .or_else(|| {
                        subfactory.for_lhs(cdr.clone()).map(|rw_cdr| {
                            View::StackCdr(car.clone(), rw_cdr)
                        })
                    }),
                _ => None,
            }
            .map(|rwv| Rewrite::validate(rwv, tag.clone()).unwrap())
        }
    }

    #[derive(Clone, Copy)]
    pub struct Reduce();
    impl Factory for Reduce {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            macro_rules! reducers {
                ($($factory:expr),*) => {None$(.or_else(|| {println!("foo {}", stringify!($factory));$factory.for_lhs(func.clone())}))*}
            };
            reducers! {
                Projection(),
                RecElimZ(),
                RecElimS(),
                EtaReductionLeft(),
                EtaReductionRight(),
                CompAssocFwd(),
                CompDistributeEmpty(),
                CompDistributeStack(),
                Recurse(*self)
            }
        }
    }
}

// #[derive(Debug, Clone)]
// pub enum PathView {
//     Refl(Func),
//     Rewrite(Rewrite),
//     Concat(Box<Path>, Box<Path>),
//     Inverse(Box<Path>),
// }

// #[derive(Debug, Clone)]
// pub struct Path(PathView);

// impl Path {
//     pub fn validate(v: PathView) -> Path {
//         if let PathView::Concat(p1, p2) = v {
//             let Endpoints(_, p1_end) = p1.endpoints();
//             let Endpoints(p2_start, _) = p2.endpoints();

//             if !p1_end.syntax_eq(&p2_start) {
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

//     pub fn endpoints(&self) -> Endpoints<Func> {
//         match self.view() {
//             PathView::Refl(f) => Endpoints(f.clone(), f.clone()),
//             PathView::Concat(p1, p2) => {
//                 let Endpoints(p1_start, _) = p1.endpoints();
//                 let Endpoints(_, p2_end) = p2.endpoints();
//                 Endpoints(p1_start, p2_end)
//             }
//             PathView::Inverse(p) => {
//                 let Endpoints(start, end) = p.endpoints();
//                 Endpoints(end, start)
//             }
//             PathView::Rewrite(rw) => Endpoints(rw.clone().lhs(), rw.clone().rhs()),
//         }
//     }
// }
use crate::rewrite::factory::Factory;

// Returns a path starting with f and leading to a reduced form.
pub fn reduce_fully(f: Func) -> Rewrite {
    println!("RED: {:?}", f);
    if let Some(rw) = factory::Reduce().for_lhs(f.clone()) {
        let rhs = rw.clone().rhs();
    println!("bar");
        let reduced = reduce_fully(rhs);
    println!("qux: {:?}", reduced);
        Rewrite::validate(View::Concat(rw, reduced), f.tag().clone()).unwrap()
    } else {
    println!("baz");
        Rewrite::validate(View::Refl(f.clone()), f.tag().clone()).unwrap()
    }
}
