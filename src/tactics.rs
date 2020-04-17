// CompAssoc(f, g, h, i): (f ~ ((g h) i)) -> (f ~ (g (h i)))
//   Rev: (f ~ (g (h i))) -> (f ~ ((g h) i))

use crate::base::{Endpoints, SyntaxEq};
use crate::func::{BadFunc, Func};
use crate::rewrite;
use std::fmt;

#[derive(Clone, Debug)]
pub struct Tactic(View);

#[derive(Clone, Debug)]
pub enum View {
    // (f, f', g) -> (f ~ f') -> ((f g) ~ (f' g))
    CompLeft(Func, Func, Func),

    // (f, g, g') -> (g ~ g') -> ((f g) ~ (f g'))
    CompRight(Func, Func, Func),
}

enum Side {
    Left,
    Right,
}

impl Tactic {
    pub fn view(&self) -> &View {
        &self.0
    }

    pub fn into_view(self) -> View {
        self.0
    }

    // pub fn endpoints(&self) -> Endpoints {
    //     match self.view() {
    //         View::CompLeft(f, f_, g) => Endpoints(Func::comp(f.clone(), g.clone()).unwrap(), Func::comp(f_.clone(), g.clone()).unwrap()),
    //         View::CompRight(f, g, g_) => Endpoints(Func::comp(f.clone(), g.clone()).unwrap(), Func::comp(f.clone(), g_.clone()).unwrap()),
    //     }
    // }

    // pub fn subgoals(&self) -> Vec<Endpoints> {
    //     match self {
    //         View::CompLeft(f, f_, _) => vec![Endpoints(f.clone(), f_.clone())],
    //         View::CompRight(f, g, g_) => vec![Endpoints(g.clone(), g_.clone())],
    //     }
    // }

    pub fn name(&self) -> &'static str {
        match self.view() {
            View::CompLeft(_, _, _) => "comp_left",
            View::CompRight(_, _, _) => "comp_right",
        }
    }

    fn try_side(self, side: Side) -> Result<Endpoints<Func>, BadFunc> {
        match self.into_view() {
            View::CompLeft(f, f_, g) => match side {
                Side::Left => Ok(Endpoints(f, f_)),
                Side::Right => Ok(Endpoints(Func::comp(f, g.clone())?, Func::comp(f_, g)?)),
            },
            View::CompRight(f, g, g_) => match side {
                Side::Left => Ok(Endpoints(g, g_)),
                Side::Right => Ok(Endpoints(Func::comp(f.clone(), g)?, Func::comp(f, g_)?)),
            },
        }
    }

    pub fn lhs(self) -> Endpoints<Func> {
        self.try_side(Side::Left).expect("validated on creation")
    }

    pub fn rhs(self) -> Endpoints<Func> {
        self.try_side(Side::Right).expect("validated on creation")
    }
}

pub enum PathView {
    // (p : (f ~ g)) -> (p ~ p)
    Refl(rewrite::Path),
    Concat(Box<Path>, Box<Path>),
    Inverse(Box<Path>),
}

pub struct Path(PathView);

impl Path {
    pub fn validate(v: PathView) -> Path {
        if let PathView::Concat(p1, p2) = v {
            let Endpoints(_, p1_end) = p1.endpoints();
            let Endpoints(p2_start, _) = p2.endpoints();

            if !p1.endpoints().end().syntax_eq(p2.endpoints().start()) {
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

    pub fn endpoints(&self) -> Endpoints<Endpoints<Func>> {
        match self.view() {
            PathView::Refl(rw) => Endpoints(rw.endpoints(), rw.endpoints()),
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

// pub enum Factory {
//     Refl,
//     Symm,
//     Rewrite(rewrite::Factory),
//     // CompLeft,
//     // CompRight,
// }

// impl Factory {
//     pub fn from_endpoints(self, Endpoints(start, end): Endpoints) -> Option<Tactic> {
//         match self {
//             Factory::Refl => {
//                 if start.syntax_eq(&end) {
//                     Some(Tactic::Refl(start))
//                 } else {
//                     None
//                 }
//             }
//             Factory::Symm => Some(Tactic::Symm(start, end)),
//             Factory::Rewrite(rwf) => {
//                 if let Some(rw) = rwf.for_func(&end) {
// Some(                    Tactic::Rewrite(start, rw))
//                 } else {
//                     None
//                 }
//             }
//         }
//     }
// }

// pub fn reduce(func : &Func) -> Goal {
//     if let Some(rw) = rewrite::Factory::CompAssocFwd.for_func(func) {
//         Goal(func)
//     }
// }

// trait Tactic {
//     fn endpoints(&self) -> Endpoints;
//     fn subgoals(&mut self) -> Vec<&mut Goal>;
// }

// trait Factory {
//     type T : Tactic;
//     fn from_endpoints(endpoints: Endpoints) -> Option<Self::T>;
// }

// struct Refl(Func);

// impl Refl {
//     fn new(f : Func) -> Self {Self(f)}
// }

// impl Tactic for Refl {
//     fn endpoints(&self)-> Endpoints {
//         let Refl(f) = self;
//         Endpoints(f.clone(), f.clone())
//     }

//     fn subgoals(&mut self) -> Vec<&mut Goal> {
//         vec![]
//     }
// }

// impl Factory for Refl {
// type  T = Refl;
//     fn from_endpoints(Endpoints(start, end): Endpoints) -> Option<Self::T> {
//         if start.syntax_eq(&end) {
//             Some(Refl(start))
//         } else {
//             None
//         }
//     }
// }

// pub struct Symm(Func, Func, Goal);

// impl Symm {
//     pub fn new(f : Func, g: Func) -> Self {Self(f.clone(), g.clone(), Goal::Active(g, f))}

//     // fn from_goal(Endpoints(start, end):Endpoints) -> Self {

//     // }
// }

// impl Tactic for Symm {
//     fn endpoints(&self)-> Endpoints {
//         let Self(f, g, _) = self;
//         Endpoints(f.clone(), g.clone())
//     }

//     fn subgoals<'a>(&'a mut self) -> Vec<&'a mut Goal> {
//         let Self(_, _, subgoal) = self;
//         vec![subgoal]
//     }
// }

// impl Factory for Symm {
// type  T = Symm;
//     fn from_endpoints(Endpoints(start, end): Endpoints) -> Option<Self::T> {
//         Some(Self::new(start, end))
//     }
// }

// pub struct RewriteFactory (pub rewrite::RuleFactory);

// impl Factory for RewriteFactory {
//     type T = Rewrite;
//     fn from_endpoints(self, Endpoints(start, end): Endpoints) -> Option<Self::T> {

//         Some(Self::new(start, end))
//     }
// }

// struct Rewrite (
//     rewrite::Rule,
// );

// impl Tactic for Rewrite {
//     fn endpoints(&self)-> Endpoints {
//         let Self(rule) = self;
//         Endpoints(rule.clone().lhs(), rule.clone().rhs())
//     }

//     fn subgoals<'a>(&'a mut self) -> Vec<&'a mut Goal> {
//         vec![]
//     }
// }

// Path 1.
//
// - Id(f): f
//   - Fwd needs: N/A
//   - Rev needs: ()
// - CompAssoc(f, g, h): ((f g) h) -> (f (g h))
//   - Fwd needs: ()
//   - Rev needs: ()
// - SkipStack(arity, car, cdr): ((skip arity) (stack car cdr)) -> cdr
//   - Fwd needs: ()
//   - Rev needs: (arity, car)
// - RecZ(z_case, s_case): ((rec z_case s_case) Z) -> z_case
//   - Fwd needs: ()
//   - Rev needs: (s_case)

// Path 2.
//
// - Refl(f): (f ~ f)
//   - Fwd needs: N/A
//   - Rev needs: ()
// - Symm(f, g): (f ~ g) -> (g ~ f)
//   - Fwd needs: ()
//   - Rev needs: ()
// - Lift(f, g, h, path1 : (f -> g)): (f ~ h) -> (g ~ h)
//   - Fwd needs: (path1)
//   - Rev needs: (path1)
// - CompLeft: (f, f', g) -> (f ~ f') -> ((f g) ~ (f' g))
//   - Rev: ((f g) ~ (f' g)) -> () -> (f ~ f')
//
// Goal is

// ProtoTrans(g).needs
//

// 3-Path
//
// Refl: (f, g, p : (f ~ g)) -> (p ~ p)
// Trans: (f, g, h, i, j, p: (i ~ j)) -> ((f ~ g) -> (h ~ i)) -> ((f ~ g) -> (h ~ j))
// - Rev: ((f ~ g) -> (h ~ j)) -> (i ~ j) -> ((f ~ g) -> (h ~ j))
//
// Goal becomes: refl ->
