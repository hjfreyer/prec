use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use func::View as FView;
use func::{BadFunc, Func};

#[derive(Clone, Debug)]
pub struct Rewrite(View, func::Tag);

#[derive(Clone, Debug)]
pub enum View {
    CompAssoc(Func, Func, Func),
    SkipStack(u32, Func, Func),
    // CompDistribute,
    // CompFactor,

    // SkipElim

    // // Composition.
    // CompDistribute,
    // EtaAbstraction,

    // // Recursion.
    // RecElimZ,
    // RecElimS,

    // Steps in nested structures.
    CompLeft(Box<Rewrite>, Func),
    CompRight(Func, Box<Rewrite>),
    // RecZ(Box<PathStep>),
    // RecS(Box<PathStep>),
    // Induction(Box<Path>),
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

            View::SkipStack(skip_arity, stack_car, stack_cdr) => match side {
                Side::Left => {
                    Func::comp(Func::skip(skip_arity)?, Func::stack(stack_car, stack_cdr)?)
                }
                Side::Right => Ok(stack_cdr),
            },

            View::CompLeft(rw_f, g) => Ok(Func::comp(rw_f.try_side(side)?, g)?),
            View::CompRight(f, rw_g) => Ok(Func::comp(f, rw_g.try_side(side)?)?),
        }
    }

    pub fn name(&self) -> &'static str {
        match self.view() {
            View::CompAssoc(_, _, _) => "comp_assoc",
            View::SkipStack(_, _, _) => "skip_stack",
            View::CompLeft(_, _) => "comp_left",
            View::CompRight(_, _) => "comp_left",
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
    //     fn preimage(self) -> Func {
    //         let CompAssoc(f, g, h) = self;
    //
    //     }
    // }
    //     }
}

pub mod factory {
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

    pub struct SkipStackFwd();

    impl Factory for SkipStackFwd {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            let tag = func.tag().clone();
            if let FView::Comp(f, g) = func.into_view() {
                if let (FView::Skip(arity), FView::Stack(car, cdr)) = (f.into_view(), g.into_view())
                {
                    Some(Rewrite::validate(View::SkipStack(arity, car, cdr), tag).unwrap())
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

#[derive(Clone,Copy)]
    pub struct Reduce();
    impl Factory for Reduce {
        fn for_lhs(&self, func: Func) -> Option<Rewrite> {
            if let Some(rw) = CompAssocFwd().for_lhs(func.clone()) {
                return Some(rw);
            }
            if let Some(rw) = SkipStackFwd().for_lhs(func.clone()) {
                return Some(rw);
            }

           if let Some(rw) = CompLeft(*self).for_lhs(func.clone()) {
                return Some(rw);
            }
if let Some(rw) = CompRight(*self).for_lhs(func.clone()) {
                return Some(rw);
            }

            None
        }
    }
}

pub enum PathView {
    Refl(Func),
    Concat(Box<Path>, Box<Path>),
    Inverse(Box<Path>),
}

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
