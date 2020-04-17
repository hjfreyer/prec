use crate::base::Endpoints;
use crate::func::Func;
use crate::tactics::Tactic;
use std::fmt;
// #[derive(Debug)]
// pub enum Goal {
//     Active(Endpoints),
//     Tactic(Tactic, Vec<Box<Goal>>),
// }

pub enum View {
    HorizontalComp,
}

pub struct VerticalPath {
    goal: Endpoints<Func>,
    tactics: Vec<Tactic>,
}

pub struct HorizontalPath {
    verticals: Vec<VerticalPath>,
}

impl HorizontalPath {
    pub fn new(start: Func, end: Func) -> Self {
        HorizontalPath {
            verticals: vec![VerticalPath {
                goal: Endpoints(start, end),
                tactics: vec![],
            }],
        }
    }
}

// impl Goal {
//     pub fn active_goal(&self) -> Option<Endpoints> {
//         match self {
//             Goal::Active(ep) => Some(ep.clone()),
//             Goal::Tactic(_, subgoals) => subgoals.iter().find_map(|sg| sg.active_goal()),
//         }
//     }

//     fn active_goal_mut(&mut self) -> Option<(&mut Goal)> {
//         match self {
//             Goal::Active(_) => Some(self),
//             Goal::Tactic(_, subgoals) => subgoals.iter_mut().find_map(|sg| sg.active_goal_mut()),
//         }
//     }

//     fn active_to_tactic(&mut self, t: Tactic) -> bool {
//         if let Goal::Active(Endpoints(start, end)) = self {
//             let Endpoints(t_start, t_end) = t.endpoints();
//             if !t_start.syntax_eq(start) || !t_end.syntax_eq(end) {
//                 return false;
//             }
//             let subgoals = t
//                 .subgoals()
//                 .into_iter()
//                 .map(|ep| Box::new(Goal::Active(ep)))
//                 .collect();
//             *self = Goal::Tactic(t, subgoals);
//             true
//         } else {
//             panic!("active_to_tactic called on tactic")
//         }
//     }

//     pub fn apply(&mut self, tf: Factory) -> bool {
//         let ag = self.active_goal_mut().unwrap();

//         if let Goal::Active(ep) = ag {
//             if let Some(t) = tf.from_endpoints(ep.clone()) {
//                 if !ag.active_to_tactic(t) {
//                     panic!("from_endpoints did the wrong thing")
//                 }
//                 return true
//             }
//             return false
//         } else {
//             panic!("active_goal_mut broken")
//         }
//     }

//     pub fn apply_tactic(&mut self, t: Tactic) -> bool {
//         self.active_goal_mut().unwrap().active_to_tactic(t)
//     }
// }

// impl fmt::Debug for Goal {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         fn print(g: &Goal, indent: u32, fmt: &mut fmt::Formatter<'_>) -> Result<bool, fmt::Error> {
//             match g {
//                 Goal::Active(Endpoints(s, e)) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     fmt.write_fmt(format_args!("{:?} -> {:?} ACTIVE\n", s, e))?;
//                     Ok(true)
//                 }
//                 Goal::Tactic(t, sg) => {
//                     for _ in 0..indent {
//                         fmt.write_str("  ")?
//                     }
//                     let Endpoints(start, end) = t.endpoints();
//                     fmt.write_fmt(format_args!("{:?} -> {:?}, {}...\n", start, end, t.name()))?;
//                     for g in sg {
//                         if print(g, indent + 1, fmt)? {
//                             return Ok(true);
//                         }
//                     }
//                     Ok(false)
//                 }
//             }
//         };
//         print(self, 0, fmt).map(|_| ())
//     }
// }
