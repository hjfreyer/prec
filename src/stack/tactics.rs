use super::actions::*;
use super::*;
use crate::base;
use crate::base::SyntaxEq;
use crate::func::Func;
use crate::path;
use crate::path::actions as pa;
use crate::tactics;

pub fn refl() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let (path::Path { start, end }, cdr) = stack.clone().snoc()?;
            if start.syntax_eq(&end) {
                Some(base::ActionChain {
                    start: cdr,
                    actions: im::vector![Action::PushRefl(start)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}

pub fn auto() -> impl base::Tactic<Action> {
    crate::tactic![
        (&& (car(path::tactics::simplify())) (refl()))
    ]
}

pub fn car<PT: base::Tactic<pa::Action>>(tactic: PT) -> impl base::Tactic<Action> {
    struct Impl<PT: base::Tactic<pa::Action>>(PT);

    impl<PT: base::Tactic<pa::Action>> base::Tactic<Action> for Impl<PT> {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let Self(tactic) = self;
            let (car, cdr) = stack.clone().snoc()?;
            let chain = tactic.react(&car)?;
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

    Impl(tactic)
}

pub fn cdr<T: base::Tactic<Action>>(tactic: T) -> impl base::Tactic<Action> {
    struct Impl<T: base::Tactic<Action>>(T);

    impl<T: base::Tactic<Action>> base::Tactic<Action> for Impl<T> {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let Self(tactic) = self;
            let (car, cdr) = stack.clone().snoc()?;
            let chain = tactic.react(&cdr)?;
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

pub fn induction() -> impl base::Tactic<Action> {
    struct Cut();
    impl base::Tactic<Action> for Cut {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let path::Path { start: f, end: rec } = stack.head()?;
            let (_z_case, s_case) = rec.unrec()?;
            let f_arity = f.arity().r#in;
            let mid = Func::rec(Func::comp(f, Func::z_eye(f_arity)).unwrap(), s_case).unwrap();
            apply_cut(&mid, stack)
        }
    }
    tactics::pipe(
        Cut(),
        tactics::pipe(
            car(path::tactics::induction()),
            cdr(car(path::tactics::rec_z())),
        ),
    )
}
