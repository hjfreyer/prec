use crate::base;
use base::Action as _;

use super::*;

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

            // Eta.
            Action::EtaReductionLeft => {
                let (eye, g) = func.decompose()?;
                if eye.syntax_eq(&Func::eye(g.arity().out)) {
                    Some(g)
                } else {
                    None
                }
            }
            Action::EtaAbstractionLeft => {
                Some(Func::comp(Func::eye(func.arity().out), func.clone()).unwrap())
            }
            Action::EtaReductionRight => {
                let (f, eye) = func.decompose()?;
                if eye.syntax_eq(&Func::eye(f.arity().r#in)) {
                    Some(f)
                } else {
                    None
                }
            }
            Action::EtaAbstractionRight => {
                Some(Func::comp(func.clone(), Func::eye(func.arity().r#in)).unwrap())
            }

            // Recursion.
            Action::RecElimZ => {
                let (rec, g) = func.decompose()?;
                let ((z_case, _s_case), (g_car, g_cdr)) = (rec.unrec()?, g.unstack()?);
                let (maybe_z, _z_args) = g_car.decompose()?;
                maybe_z.unz()?;

                Some(Func::comp(z_case, g_cdr).unwrap())
            }
            Action::RecElimS => {
                let (rec, g) = func.decompose()?;
                let ((_z_case, s_case), (g_car, g_cdr)) = (rec.unrec()?, g.unstack()?);
                let (maybe_s, s_args) = g_car.decompose()?;
                let ((), (s_args_car, _s_args_cdr)) = (maybe_s.uns()?, s_args.unstack()?);

                let decremented_args = Func::stack(s_args_car, g_cdr).unwrap();
                let rec_call = Func::comp(rec, decremented_args.clone()).unwrap();

                Some(Func::comp(s_case, Func::stack(rec_call, decremented_args).unwrap()).unwrap())
            }

            Action::CompLeft(f_action) => {
                let (f, g) = func.decompose()?;
                let f2 = f_action.act(f).ok()?;
                Some(Func::comp(f2, g).unwrap())
            }
            Action::CompRight(g_action) => {
                let (f, g) = func.decompose()?;
                let g2 = g_action.act(g).ok()?;
                Some(Func::comp(f, g2).unwrap())
            }             
            Action::StackCar(action) => {
                let (car, cdr) = func.unstack()?;
                let car2 = action.act(car).ok()?;
                Some(Func::stack(car2, cdr).unwrap())
            }
            Action::StackCdr(action) => {
                let (car, cdr) = func.unstack()?;
                Some(Func::stack(car, action.act(cdr).ok()?).unwrap())
            }
            Action::RecZ(action) => {
                let (z_case, s_case) = func.unrec()?;
                Some(Func::rec(action.internal_apply(&z_case)?, s_case).unwrap())
            }
            Action::RecS(action) => {
                let (z_case, s_case) = func.unrec()?;
                Some(Func::rec(z_case, action.internal_apply(&s_case)?).unwrap())
            }            
            Action::Inverse(f, action) => {
                if func.syntax_eq(&action.internal_apply(f).unwrap()) 
                {
                    Some(f.clone())
                } else {
                    None
                }
            }
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
