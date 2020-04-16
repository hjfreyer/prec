// CompAssoc(f, g, h, i): (f ~ ((g h) i)) -> (f ~ (g (h i)))
//   Rev: (f ~ (g (h i))) -> (f ~ ((g h) i))

use crate::func::Func;
use crate::rewrite;
use std::fmt;

// #[derive(Debug)]
pub enum Goal {
    Active(Endpoints),
    Tactic(Tactic, Vec<Box<Goal>>),
}

impl Goal {
    pub fn active_goal(&self) -> Option<Endpoints> {
        match self {
            Goal::Active(ep) => Some(ep.clone()),
            Goal::Tactic(_, subgoals) => subgoals.iter().find_map(|sg| sg.active_goal()),
        }
    }

    fn active_goal_mut(&mut self) -> Option<(&mut Goal)> {
        match self {
            Goal::Active(_) => Some(self),
            Goal::Tactic(_, subgoals) => subgoals.iter_mut().find_map(|sg| sg.active_goal_mut()),
        }
    }

    fn active_to_tactic(&mut self, t: Tactic) -> bool {
        if let Goal::Active(Endpoints(start, end)) = self {
            let Endpoints(t_start, t_end) = t.endpoints();
            if !t_start.syntax_eq(start) || !t_end.syntax_eq(end) {
                return false;
            }
            let subgoals = t
                .subgoals()
                .into_iter()
                .map(|ep| Box::new(Goal::Active(ep)))
                .collect();
            *self = Goal::Tactic(t, subgoals);
            true
        } else {
            panic!("active_to_tactic called on tactic")
        }
    }

    pub fn apply(&mut self, tf: Factory) -> &mut Self {
        let ag = self.active_goal_mut().unwrap();

        if let Goal::Active(ep) = ag {
            if let Some(t) = tf.from_endpoints(ep.clone()) {
                if !ag.active_to_tactic(t) {
                    panic!("from_endpoints did the wrong thing")
                }
            }
            self
        } else {
            panic!("active_goal_mut broken")
        }
    }

    pub fn apply_tactic(&mut self, t: Tactic) -> &mut Self {
        self.active_goal_mut().unwrap().active_to_tactic(t);
        self
    }
}

impl fmt::Debug for Goal {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn print(g: &Goal, indent: u32, fmt: &mut fmt::Formatter<'_>) -> Result<bool, fmt::Error> {
            match g {
                Goal::Active(Endpoints(s, e)) => {
                    for _ in 0..indent {
                        fmt.write_str("  ")?
                    }
                    fmt.write_fmt(format_args!("{:?} -> {:?} ACTIVE\n", s, e))?;
                    Ok(true)
                }
                Goal::Tactic(t, sg) => {
                    for _ in 0..indent {
                        fmt.write_str("  ")?
                    }
                    let Endpoints(start, end) = t.endpoints();
                    fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, t.name()))?;
                    for g in sg {
                        if print(g, indent + 1, fmt)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }
            }
        };
        print(self, 0, fmt).map(|_| ())
    }
}

#[derive(Debug, Clone)]
pub struct Endpoints(pub Func, pub Func);

#[derive(Debug)]
pub enum Tactic {
    Refl(Func),
    Symm(Func, Func),
}

impl Tactic {
    pub fn endpoints(&self) -> Endpoints {
        match self {
            Tactic::Refl(f) => Endpoints(f.clone(), f.clone()),
            Tactic::Symm(f, g) => Endpoints(f.clone(), g.clone()),
        }
    }

    pub fn subgoals(&self) -> Vec<Endpoints> {
        match self {
            Tactic::Refl(_) => vec![],
            Tactic::Symm(f, g) => vec![Endpoints(g.clone(), f.clone())],
        }
    }

    pub fn name(&self) -> &'static str {
        match self {
Tactic::Refl(_) => "refl",
Tactic::Symm(_, _) => "symm",
        }
    }
}

pub enum Factory {
    Refl,
    Symm,
}

impl Factory {
    pub fn from_endpoints(self, Endpoints(start, end): Endpoints) -> Option<Tactic> {
        match self {
            Factory::Refl => {
                if start.syntax_eq(&end) {
                    Some(Tactic::Refl(start))
                } else {
                    None
                }
            }
            Factory::Symm => Some(Tactic::Symm(start, end)),
        }
    }
}

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
