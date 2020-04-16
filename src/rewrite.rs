use crate::func;
use func::{BadFunc, Func};
use func::View as FView;

#[derive(Clone, Debug)]
pub struct Rule(View);

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

    // // Steps in nested structures.
    // CompLeft(Box<PathStep>),
    // CompRight(usize, Box<PathStep>),
    // RecZ(Box<PathStep>),
    // RecS(Box<PathStep>),
    // Induction(Box<Path>),
}


#[derive(Clone, Debug, Copy)]
pub enum Factory {
    CompAssocFwd,
    CompAssocRev,

    SkipStackFwd,
    // CompDistribute,
    // CompFactor,

    // SkipElim

    // // Composition.
    // CompDistribute,
    // EtaAbstraction,

    // // Recursion.
    // RecElimZ,
    // RecElimS,

    // // Steps in nested structures.
    // CompLeft(Box<PathStep>),
    // CompRight(usize, Box<PathStep>),
    // RecZ(Box<PathStep>),
    // RecS(Box<PathStep>),
    // Induction(Box<Path>),
}

impl Factory {
    pub fn for_func(self, func: &Func) -> Option<Rule> {
        match self {
            Factory::CompAssocFwd => {
                if let FView::Comp(fg, h) = func.view() {
                    if let FView::Comp(f, g) = fg.view() {
                        return Some(
                            Rule::validate(View::CompAssoc(f.clone(), g.clone(), h.clone()))
                                .unwrap(),
                        );
                    }
                }
                None
            }
            Factory::CompAssocRev => {
                if let FView::Comp(f, gh) = func.view() {
                    if let FView::Comp(g, h) = gh.view() {
                        return Some(
                            Rule::validate(View::CompAssoc(f.clone(), g.clone(), h.clone()))
                                .unwrap(),
                        );
                    }
                }
                None
            }
            Factory::SkipStackFwd => {
                if let FView::Comp(f, g) = func.view() {
                    if let (FView::Skip(arity), FView::Stack(car, cdr)) = (f.view(), g.view()) {
                        return Some(
                            Rule::validate(View::SkipStack(*arity, car.clone(), cdr.clone()))
                                .unwrap(),
                        );
                    }
                }
                None
            } //     fn from_image(func: &Func) -> Result<Self> {
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
        }
    }
}


enum Side {
    Left,
    Right,
}

impl Rule {
    // pub fn comp_assoc(f: Func, g: Func, h: Func) -> Result<Rule, BadFunc> {
    //     Rule(View::CompAssoc(f, g, h)).validate();
    // }

    // pub fn skip_stack(skip_arity: u32, stack_car: Func, stack_cdr: Func) -> Result<Rule, BadFunc> {
    //     Rule(View::SkipStack(skip_arity, stack_car, stack_cdr)).validate()
    // }

    pub fn validate(view: View) -> Result<Rule, BadFunc> {
        let res = Rule(view);
        res.clone().try_side(Side::Left)?;
        res.clone().try_side(Side::Right)?;
        Ok(res)
    }

    // pub fn match_rule(view : View) -> Result<Rule, BadFunc> {

    // }

    fn try_side(self, side: Side) -> Result<Func, BadFunc> {
        match self.0 {
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
        }
    }

    pub fn lhs(self) -> Func {
        self.try_side(Side::Left).expect("validated on creation")
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
pub enum Path {
    Identity(Func),
    Step(Box<Path>, Rule),
    Inverse(Box<Path>),
}

// pub enum Rule2View {
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

// pub fn rewrite(func: Func, rule: Rule) -> Func {

// }

// pub enum Result<R: Rule> {
//     None,
//     Some(R),
//     Underconstrained,
// }

// pub trait Rule {
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

// impl Rule for CompAssoc {
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

// impl Rule for SkipStack {
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

// pub trait Rule2D {
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
// enum Rule {
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
