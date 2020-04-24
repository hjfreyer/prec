use crate::actions::func as fa;
use crate::base;
use crate::func::Func;
use base::Action as _;

#[derive(Clone, Debug)]
pub struct Path {
    pub start: Func,
    pub end: Func,
}

impl base::Point for Path {}
impl base::SyntaxEq for Path {
    fn syntax_eq(&self, other: &Self) -> bool {
        self.start.syntax_eq(&other.start) && self.end.syntax_eq(&other.end)
    }
}

#[derive(Debug)]
pub enum Error {
    NotApplicable(Action, Path),
}

#[derive(Clone, Debug)]
pub enum Action {
    ActOnStart(fa::Action),
    ActOnEnd(fa::Action),

    Reverse,

    // Induction.
    Induction,

    // Upgrade a path to one inside a nested structure.
    CompLeft(Func),
    CompRight(Func),
    StackCar(Func),
    StackCdr(Func),
    RecZ(Func),
    RecS(Func),
}

impl Action {
    fn internal_act(&self, path: Path) -> Option<Path> {
        match self {
            Action::ActOnStart(fa) => Some(Path {
                start: fa.act(path.start).ok()?,
                end: path.end,
            }),
            Action::ActOnEnd(fa) => Some(Path {
                start: path.start,
                end: fa.act(path.end).ok()?,
            }),
            Action::Reverse => Some(Path {
                start: path.end,
                end: path.start,
            }),
            _ => unimplemented!(),
        }
    }
}

impl base::Action for Action {
    type Point = Path;
    type Error = Error;

    fn act(&self, path: Path) -> Result<Path, Error> {
        if let Some(res) = self.internal_act(path.clone()) {
            Ok(res)
        } else {
            Err(Error::NotApplicable(self.clone(), path))
        }
    }
}

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


pub fn induction() -> impl Tactic {
    struct Impl();
    impl Tactic for Impl {
        fn apply(
            &self,
            Path{start: f, end: rec}: &Path,
        ) -> Option<base::ActionChain<Action>> {
            let f_arity = f.arity().r#in;
            let (z_case, s_case) = rec.unrec()?;
            let (z_f, z_g) = z_case.decompose()?;
            if !z_f.syntax_eq(f) || !z_g.syntax_eq(&Func::z_eye(f_arity)) {
                return None;
            }

            let start_start = Func::comp(f.clone(), Func::s_eye(f_arity)).unwrap();
            let start_end = Func::comp(
                s_case.clone(),
                Func::stack(f.clone(), Func::eye(f_arity)).unwrap(),
            )
            .unwrap();

            Some((
                Endpoints(start_start, start_end),
                im::vector![Action(View::Induction)],
            ))
        }
    }
    Impl()
}