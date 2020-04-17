use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use func::View as FView;
use func::{BadFunc, Func};

#[derive(Clone, Debug)]
pub struct Rewrite(View, func::Tag);

#[derive(Clone, Debug)]
pub enum View {
    CompAssoc(Func, Func, Func),
    CompDistributeEmpty(Func),
    CompDistributeStack(Func, Func, Func),

    SkipStack(Func, Func),
    SelectStack(Func, Func),
    Stackify(Func),

    EtaAbstractionLeft(Func),
    EtaReductionLeft(Func),
    EtaAbstractionRight(Func),
    EtaReductionRight(Func),

    // // Recursion.
    RecElimZ(Func, Func, Func, Func),
    // RecElimS,

    // Steps in nested structures.
    CompLeft(Box<Rewrite>, Func),
    CompRight(Func, Box<Rewrite>),
    StackCar(Box<Rewrite>, Func),
    StackCdr(Func, Box<Rewrite>),
    // RecZ(Box<PathStep>),
    // RecS(Box<PathStep>),
    Induction(Func, Func, Box<Path>),
}

enum Side {
    Left,
    Right,
}

impl Rewrite {
    pub fn view(&self) -> &View {
        &self.0
    }
    pub fn into_view(self) -> View {
        self.0
    }
    // pub fn comp_assoc(f: Func, g: Func, h: Func) -> Result<Rewrite, BadFunc> {
    //     Rewrite(View::CompAssoc(f, g, h)).validate();
    // }

    // pub fn skip_stack(skip_arity: u32, stack_car: Func, stack_cdr: Func) -> Result<Rewrite, BadFunc> {
    //     Rewrite(View::SkipStack(skip_arity, stack_car, stack_cdr)).validate()
    // }

    pub fn validate(view: View, tag: func::Tag) -> Result<Rewrite, BadFunc> {
        let res = Rewrite(view, tag);
        res.clone().try_side(Side::Left)?;
        res.clone().try_side(Side::Right)?;
        Ok(res)
    }

    // pub fn match_Rewrite(view : View) -> Result<Rewrite, BadFunc> {

    // }

    fn try_side(self, side: Side) -> Result<Func, BadFunc> {
        match self.into_view() {
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
            View::SkipStack(stack_car, stack_cdr) => match side {
                Side::Left => {
                    let skip_arity = stack_cdr.arity().out() + 1;
                    Func::comp(Func::skip(skip_arity)?, Func::stack(stack_car, stack_cdr)?)
                }
                Side::Right => Ok(stack_cdr),
            },
            View::SelectStack(stack_car, stack_cdr) => match side {
                Side::Left => {
                    let select_arity = stack_cdr.arity().out() + 1;
                    Func::comp(
                        Func::select(select_arity)?,
                        Func::stack(stack_car, stack_cdr)?,
                    )
                }
                Side::Right => Ok(stack_car),
            },
            View::Stackify(f) => match side {
                Side::Left => Ok(f),
                Side::Right => {
                    let f_in = f.arity().r#in();
                    Func::stack(
                        f,
                    Func::empty(f_in)
                    )
                }
            },

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

            View::RecElimZ(z_case, s_case, z_args, other_args) => match side {
                Side::Left => Ok(Func::comp(
                    Func::rec(z_case, s_case)?,
                    Func::stack(Func::comp(Func::z(), z_args)?, other_args)?,
                )?),
                Side::Right => Ok(Func::comp(z_case, other_args)?),
            },

            View::CompLeft(rw_f, g) => Ok(Func::comp(rw_f.try_side(side)?, g)?),
            View::CompRight(f, rw_g) => Ok(Func::comp(f, rw_g.try_side(side)?)?),
            View::StackCar(rw_car, cdr) => Ok(Func::stack(rw_car.try_side(side)?, cdr)?),
            View::StackCdr(car, rw_cdr) => Ok(Func::stack(car, rw_cdr.try_side(side)?)?),
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
        }
    }

    // pub fn name(&self) -> &'static str {
    //     match self.view() {
    //         View::CompAssoc(_, _, _) => "comp_assoc",
    //         View::SkipStack(_, _, _) => "skip_stack",
    //         View::SelectStack(_, _, _) => "select_stack",
    //         View::CompLeft(_, _) => "comp_left",
    //         View::CompRight(_, _) => "comp_left",
    //         View::Induction(_, _, _) => "induction",
    //     }
    // }

    pub fn lhs(self) -> Func {
        let tag = self.1.clone();
        self.try_side(Side::Left)
            .expect("validated on creation")
            .set_tag(tag)
    }

    pub fn rhs(self) -> Func {
        self.try_side(Side::Right).expect("validated on creation")
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

    pub struct SkipStackFwd();
    impl Factory for SkipStackFwd {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Skip(_), FView::Stack(car, cdr)) = (f.into_view(), g.into_view()) {
                    Some(Rewrite::validate(View::SkipStack(car, cdr), tag).unwrap())
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct SelectStackFwd();
    impl Factory for SelectStackFwd {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Select(_), FView::Stack(car, cdr)) = (f.into_view(), g.into_view()) {
                    Some(Rewrite::validate(View::SelectStack(car, cdr), tag).unwrap())
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
                    Some(Rewrite::validate(View::EtaReductionLeft(f), tag).unwrap())
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

    // Statements that necessarily have an arity-one output should be wrapped in a stack
    // when composed.
    pub struct FixUnstackedComps();
    impl Factory for FixUnstackedComps {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                match g.view() {
                    FView::Z | FView::S | FView::Select(_) | FView::Rec(_, _) => {
let abstract_g = Rewrite::validate(View::Stackify(g), 
                                    func::Tag::None).unwrap();
                       Some(
                                Rewrite::validate(
                                    View::CompRight(f, Box::new(abstract_g)),
                                    tag,
                                )
                                .unwrap(),
                            )
                    }
                    _ => None
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
                if let (FView::Rec(z_case, s_case), FView::Stack(car, other_args)) = (f.view(), g.view()) {
                    match car.view() {
                        FView::Z => {
                            let z_eta_abstract = Rewrite::validate(
                                View::EtaAbstractionRight(Func::z()),
                                func::Tag::None,
                            )
                            .unwrap();
                            let inside_stack = Rewrite::validate(
                                View::StackCar(Box::new(z_eta_abstract), other_args.clone()),
                                func::Tag::None,
                            )
                            .unwrap();
                            Some(
                                Rewrite::validate(
                                    View::CompRight(f, Box::new(inside_stack)),
                                    tag,
                                )
                                .unwrap(),
                            )
                        },
                        FView::Comp(f, z_args) => {
                            if let FView::Z = f.view() {
                                                            Some(
                                Rewrite::validate(
                                    View::RecElimZ(z_case.clone(), s_case.clone(), z_args.clone(), other_args.clone()),
                                    tag,
                                )
                                .unwrap(),
                            )
                            } else {
                                None
                            }
                        }
                        _=> None
                    }
                } else {
                    None
                }
            } else {
                None
            }
        }
    }

    pub struct CompLeft<T: Factory>(T);
    impl<T: Factory> Factory for CompLeft<T> {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let CompLeft(subfactory) = self;
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                subfactory
                    .for_lhs(f)
                    .map(|rw_f| Rewrite::validate(View::CompLeft(Box::new(rw_f), g), tag).unwrap())
            } else {
                None
            }
        }
    }

    pub struct CompRight<T: Factory>(T);
    impl<T: Factory> Factory for CompRight<T> {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let CompRight(subfactory) = self;
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                subfactory
                    .for_lhs(g)
                    .map(|rw_g| Rewrite::validate(View::CompRight(f, Box::new(rw_g)), tag).unwrap())
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
            match func.view() {
                FView::Comp(f, g) => None
                    .or_else(|| {
                        subfactory
                            .for_lhs(f.clone())
                            .map(|rw_f| View::CompLeft(Box::new(rw_f), g.clone()))
                    })
                    .or_else(|| {
                        subfactory
                            .for_lhs(g.clone())
                            .map(|rw_g| View::CompRight(f.clone(), Box::new(rw_g)))
                    }),                
                FView::Stack(car, cdr) => None
                    .or_else(|| {
                        subfactory
                            .for_lhs(car.clone())
                            .map(|rw_car| View::StackCar(Box::new(rw_car), cdr.clone()))
                    })
                    .or_else(|| {
                        subfactory
                            .for_lhs(cdr.clone())
                            .map(|rw_cdr| View::CompRight(car.clone(), Box::new(rw_cdr)))
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
                ($($factory:expr),*) => {None$(.or_else(|| $factory.for_lhs(func.clone())))*}
            };
 reducers! {
                CompAssocFwd(),
                CompDistributeEmpty(),
                CompDistributeStack(),
                SkipStackFwd(),
                SelectStackFwd(),
                RecElimZ(),
                EtaReductionLeft(),
                EtaReductionRight(),
                Recurse(*self),
                FixUnstackedComps()
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum PathView {
    Refl(Func),
    Concat(Box<Path>, Box<Path>),
    Inverse(Box<Path>),
}

#[derive(Debug, Clone)]
pub struct Path(PathView);

// #[derive(Debug, Clone)]
// pub struct Endpoints(pub Func, pub Func);

impl Path {
    pub fn validate(v: PathView) -> Path {
        if let PathView::Concat(p1, p2) = v {
            let Endpoints(_, p1_end) = p1.endpoints();
            let Endpoints(p2_start, _) = p2.endpoints();

            if !p1_end.syntax_eq(&p2_start) {
                panic!("vewwy bad")
            }
            Path(PathView::Concat(p1, p2))
        } else {
            Path(v)
        }
    }

    pub fn view(&self) -> &PathView {
        &self.0
    }

    pub fn endpoints(&self) -> Endpoints<Func> {
        match self.view() {
            PathView::Refl(f) => Endpoints(f.clone(), f.clone()),
            PathView::Concat(p1, p2) => {
                let Endpoints(p1_start, _) = p1.endpoints();
                let Endpoints(_, p2_end) = p2.endpoints();
                Endpoints(p1_start, p2_end)
            }
            PathView::Inverse(p) => {
                let Endpoints(start, end) = p.endpoints();
                Endpoints(end, start)
            }
        }
    }
}

// pub enum Path {
//     Identity(Func),
//     Step(Box<Path>, Rewrite),
//     Inverse(Box<Path>),
// }

// pub enum Rewrite2View {
//     // (f -> f') => ((f g) -> (f' g))
//     CompLeft(Func)

//     // ((f S) -> (g f id)) => (f -> (rec (f Z) g))
//     Induction,

//     // ((f z) -> x) => f -> (rec x (fun r n. (f n)))
// }

// Want to prove: f -> (rec (f Z) g)
//
// rec-embed: (rec (f Z) (|r, n| (f (S n)))) -> (rec (f Z) g)
// rec-s: (|r, n| (f (S n))) -> g

// pub fn rewrite(func: Func, Rewrite: Rewrite) -> Func {

// }

// pub enum Result<R: Rewrite> {
//     None,
//     Some(R),
//     Underconstrained,
// }

// pub trait Rewrite {
//     fn from_preimage(func: &Func) -> Result<Self>
//     where
//         Self: Sized;
//     fn from_image(func: &Func) -> Result<Self>
//     where
//         Self: Sized;
//     fn preimage(self) -> Func;
//     fn image(self) -> Func;
// }

// pub struct CompAssoc(Func, Func, Func);

// impl Rewrite for CompAssoc {
//     fn from_preimage(func: &Func) -> Result<Self> {
//         if let FView::Comp(f, h) = func.view() {
//             if let FView::Comp(f, g) = f.view() {
//                 return Result::Some(CompAssoc( f.clone(),
//                     g.clone(),
//                      h.clone(),
//                 ));
//             }
//         }
//         Result::None
//     }
//     fn from_image(func: &Func) -> Result<Self> {
//         if let FView::Comp(f, g) = func.view() {
//             if let FView::Comp(g, h) = g.view() {
//                 return Result::Some(CompAssoc (
//                      f.clone(),
//                      g.clone(),
//                      h.clone(),
//                 ));
//             }
//         }
//         Result::None
//     }
//     fn image(self) -> Func {
//         let CompAssoc(f, g, h) = self;
//         Func::comp(f, Func::comp(g, h).unwrap()).unwrap()
//     }
//     fn preimage(self) -> Func {
//         let CompAssoc(f, g, h) = self;
//         Func::comp(Func::comp(f, g).unwrap(), h).unwrap()
//     }
// }

// pub struct SkipStack(u32, Func, Func);

// impl Rewrite for SkipStack {
//     fn from_preimage(func: &Func) -> Result<Self> {
//         if let FView::Comp(f, g) = func.view() {
//             if let (FView::Skip(arity), FView::Stack(car, cdr)) = (f.view(), g.view()) {
//                 return Result::Some(Self(*arity, car.clone(), cdr.clone()))
//             }
//         }
//         Result::None
//     }
//     fn from_image(_func: &Func) -> Result<Self> {
//         Result::Underconstrained
//     }
//     fn image(self) -> Func {
//         let Self(_, _, cdr) = self;
//         cdr
//     }
//     fn preimage(self) -> Func {
//         let Self(arity, car, cdr) = self;
//         Func::comp(Func::skip(arity).unwrap(), Func::comp(car, cdr).unwrap()).unwrap()
//     }
// }

// enum Path2D {
//     Reflexive(Func),
//     HorizontalComposition(Path2D, Path2D)
// }

// pub trait Rewrite2D {
//     fn from_preimage(start: &Func, end: &Func) -> Result<Self>
//     where
//         Self: Sized;
//     fn from_image(func: &Func) -> Result<Self>
//     where
//         Self: Sized;
//     fn preimage(self) -> Func;
//     fn image(self) -> Func;
// }

// #[derive(Clone, Debug)]
// enum Rewrite {
//     SkipElim

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
