use crate::base;
use crate::func::actions as fa;
use crate::func::Func;
use base::Action as _;

use super::*;

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
