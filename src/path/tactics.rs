use super::actions::*;
use super::*;
use crate::base;
use crate::func::actions as fa;

impl<T: base::Tactic<fa::Action>> base::Tactic<Action> for T {
    fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
        let chain = self.react(end)?;
        Some(base::ActionChain {
            start: Path {
                start: start.clone(),
                end: chain.start,
            },
            actions: chain
                .actions
                .into_iter()
                .map(|a| Action::ActOnEnd(a))
                .collect(),
        })
    }
}

// pub fn induction() -> impl Tactic {
//     struct Impl();
//     impl Tactic for Impl {
//         fn apply(
//             &self,
//             Path{start: f, end: rec}: &Path,
//         ) -> Option<base::ActionChain<Action>> {
//             let f_arity = f.arity().r#in;
//             let (z_case, s_case) = rec.unrec()?;
//             let (z_f, z_g) = z_case.decompose()?;
//             if !z_f.syntax_eq(f) || !z_g.syntax_eq(&Func::z_eye(f_arity)) {
//                 return None;
//             }

//             let start_start = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
//             let start_end = Func::comp(
//                 s_case.clone(),
//                 Func::stack(f.clone(), Func::eye(f_arity)).unwrap(),
//             )
//             .unwrap();

//             Some((
//                 Endpoints(start_start, start_end),
//                 im::vector![Action(View::Induction)],
//             ))
//         }
//     }
//     Impl()
// }
