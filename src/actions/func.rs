use crate::base;
use crate::func::Func;
use base::Action as _;

#[derive(Debug)]
pub enum Error {
    NotApplicable(Action, Func),
}

#[derive(Clone, Debug)]
pub enum Action {
    // Projection
    ProjCar,
    ProjCdr,

    // Composition.
    CompAssocRight,
    CompDistributeEmpty,
    CompDistributeStack,

    // Eta.
    EtaReductionLeft,
    EtaAbstractionLeft,
    EtaReductionRight,
    EtaAbstractionRight,

    // Recursion.
    RecElimZ,
    RecElimS,

    // Steps in nested structures.
    CompLeft(Box<Action>),
    CompRight(Box<Action>),
    StackCar(Box<Action>),
    StackCdr(Box<Action>),
    RecZ(Box<Action>),
    RecS(Box<Action>),

    // TODO: make this less inefficient.
    Inverse(Func, Box<Action>),
}

impl Action {
    fn internal_apply(&self, func: &Func) -> Option<Func> {
        match self {
            Action::ProjCar => {
                let (f, g) = func.decompose()?;
                let ((select, _), (car, _)) = (f.unproj()?, g.unstack()?);
                if select == 0 {
                    Some(car)
                } else {
                    None
                }
            }
            Action::ProjCdr => {
                let (f, g) = func.decompose()?;
                let ((select, arity), (_, cdr)) = (f.unproj()?, g.unstack()?);
                if 0 < select {
                    Some(Func::comp(Func::proj(select - 1, arity - 1).unwrap(), cdr).unwrap())
                } else {
                    None
                }
            }
            Action::CompAssocRight => {
                let (fg, h) = func.decompose()?;
                let (f, g) = fg.decompose()?;
                Some(Func::comp(f, Func::comp(g, h).unwrap()).unwrap())
            }
            Action::CompDistributeEmpty => {
                let (empty, g) = func.decompose()?;
                empty.unempty()?;
                Some(Func::empty(g.arity().r#in))
            }
            Action::CompDistributeStack => {
                let (stack, g) = func.decompose()?;
                let (car, cdr) = stack.unstack()?;
                Some(
                    Func::stack(
                        Func::comp(car, g.clone()).unwrap(),
                        Func::comp(cdr, g.clone()).unwrap(),
                    )
                    .unwrap(),
                )
            }
            _ => unimplemented!(),
        }
    }
}

impl base::Action for Action {
    type Point = Func;
    type Error = Error;
    fn act(&self, func: Func) -> Result<Func, Error> {
        if let Some(res) = self.internal_apply(&func) {
            Ok(res)
        } else {
            Err(Error::NotApplicable(self.clone(), func))
        }
    }
}

impl base::Tactic<Action> for Action {
    fn react(&self, func: &Func) -> Option<base::ActionChain<Action>> {
        let rewritten = self.act(func.clone()).ok()?;
        Some(base::ActionChain {
            start: rewritten,
            actions: im::vector![Action::Inverse(func.clone(), Box::new(self.clone()))],
        })
    }
}
