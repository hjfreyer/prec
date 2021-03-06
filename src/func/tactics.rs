use super::actions::*;
use super::*;
use crate::base;
use crate::base::Action as _;
use crate::func;
use crate::tactic;

impl base::Tactic<Action> for Action {
    fn react(&self, func: &Func) -> Option<base::ActionChain<Action>> {
        let rewritten = self.act(func.clone()).ok()?;
        Some(base::ActionChain {
            start: rewritten,
            actions: im::vector![Action::Inverse(func.clone(), Box::new(self.clone()))],
        })
    }
}

pub fn eta_abstract_bare_z_or_s() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, func: &Func) -> Option<base::ActionChain<Action>> {
            let (f, g) = func.decompose()?;
            f.unrec()?;
            let (g_car, _g_cdr) = g.unstack()?;
            if let func::View::Z | func::View::S = g_car.view() {
                let eta_abs = Action::EtaAbstractionRight;

                let g_rw = Action::StackCar(Box::new(eta_abs));

                Action::CompRight(Box::new(g_rw)).react(func)
            } else {
                None
            }
        }
    }
    Impl()
}

pub fn reduce_once() -> impl base::Tactic<Action> {
    tactic![
        (|| (RecursiveTactic(Action::ProjCar))(RecursiveTactic(Action::ProjCdr))(RecursiveTactic(
            Action::CompAssocRight
        ))(RecursiveTactic(Action::CompDistributeStack))(RecursiveTactic(
            Action::CompDistributeEmpty
        ))(RecursiveTactic(Action::RecElimZ))(RecursiveTactic(Action::RecElimS))(
            RecursiveTactic(Action::EtaReductionLeft)
        )(RecursiveTactic(Action::EtaReductionRight))(RecursiveTactic(
            eta_abstract_bare_z_or_s()
        )))
    ]
}

struct RecursiveTactic<T: base::Tactic<Action>>(T);
impl<T: base::Tactic<Action>> base::Tactic<Action> for RecursiveTactic<T> {
    fn react(&self, end_func: &Func) -> Option<base::ActionChain<Action>> {
        let Self(tactic) = self;
        if let res @ Some(_) = tactic.react(end_func) {
            return res;
        }
        if let Some((f, g)) = end_func.decompose() {
            let opt = None
                .or_else(|| {
                    let chain = self.react(&f)?;
                    Some(base::ActionChain {
                        start: Func::comp(chain.start, g.clone()).unwrap(),
                        actions: chain
                            .actions
                            .into_iter()
                            .map(|a| Action::CompLeft(Box::new(a)))
                            .collect(),
                    })
                })
                .or_else(|| {
                    let chain = self.react(&g)?;
                    Some(base::ActionChain {
                        start: Func::comp(f.clone(), chain.start).unwrap(),
                        actions: chain
                            .actions
                            .into_iter()
                            .map(|a| Action::CompRight(Box::new(a)))
                            .collect(),
                    })
                });
            if let Some(p) = opt {
                return Some(p);
            }
        }
        if let Some((car, cdr)) = end_func.unstack() {
            let opt = None
                .or_else(|| {
                    let chain = self.react(&car)?;
                    Some(base::ActionChain {
                        start: Func::stack(chain.start, cdr.clone()).unwrap(),
                        actions: chain
                            .actions
                            .into_iter()
                            .map(|a| Action::StackCar(Box::new(a)))
                            .collect(),
                    })
                })
                .or_else(|| {
                    let chain = self.react(&cdr)?;
                    Some(base::ActionChain {
                        start: Func::stack(car.clone(), chain.start).unwrap(),
                        actions: chain
                            .actions
                            .into_iter()
                            .map(|a| Action::StackCdr(Box::new(a)))
                            .collect(),
                    })
                });
            if let Some(p) = opt {
                return Some(p);
            }
        }
        None
    }
}
