use super::actions::*;
use super::*;
use crate::base;
use crate::func::Func;
use crate::path;
use crate::path::actions as pa;

impl<P: base::Tactic<pa::Action>> base::Tactic<Action> for P {
    fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
        let (car, cdr) = stack.clone().snoc()?;
        let chain = self.react(&car)?;
        Some(base::ActionChain {
            start: cdr.push(chain.start),
            actions: chain
                .actions
                .into_iter()
                .map(|a| Action::CarApply(a))
                .collect(),
        })
    }
}

pub fn cdr<T: base::Tactic<Action>>(tactic: T) -> impl base::Tactic<Action> {
    struct Impl<T: base::Tactic<Action>>(T);

    impl<T: base::Tactic<Action>> base::Tactic<Action> for Impl<T> {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let (car, cdr) = stack.clone().snoc()?;
            let chain = self.react(&cdr)?;
            Some(base::ActionChain {
                start: chain.start.push(car),
                actions: chain
                    .actions
                    .into_iter()
                    .map(|a| Action::CdrApply(Box::new(a)))
                    .collect(),
            })
        }
    }
    Impl(tactic)
}

fn apply_cut(mid: &Func, stack: &Stack) -> Option<base::ActionChain<Action>> {
    let (path::Path { start, end }, cdr) = stack.clone().snoc()?;
    let new_stack = cdr
        .push(path::Path {
            start: mid.clone(),
            end,
        })
        .push(path::Path {
            start,
            end: mid.clone(),
        });
    Some(base::ActionChain {
        start: new_stack,
        actions: im::vector![Action::HorizontalConcat],
    })
}

pub fn cut(func: &Func) -> impl base::Tactic<Action> {
    struct Impl(Func);
    impl base::Tactic<Action> for Impl {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let Self(mid) = self;
            apply_cut(mid, stack)
        }
    }
    Impl(func.clone())
}
