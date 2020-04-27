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

pub fn swap() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let (car, cdr) = stack.clone().snoc()?;
            let (car_cdr, cdr_cdr) = cdr.snoc()?;
            Some(base::ActionChain {
                start: cdr_cdr.push(car).push(car_cdr),
                actions: im::vector![Action::Swap],
            })
        }
    }
    Impl()
}

pub fn auto() -> impl base::Tactic<Action> {
    crate::tactic![(&&(car(path::tactics::simplify()))(refl()))]
}

pub fn turbo() -> impl base::Tactic<Action> {
    crate::tactic![(*(|| (refl())(simplify())(induction())))]
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

pub fn apply_and_cut<F>(f1: F) -> impl base::Tactic<Action>
where
    F: Fn(&Func) -> Func,
{
    struct Impl<F: Fn(&Func) -> Func>(F);
    impl<F: Fn(&Func) -> Func> base::Tactic<Action> for Impl<F> {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let Self(f1) = self;
            let path::Path { start, end } = stack.head()?;
            double_cut(&f1(&start), &f1(&end)).react(stack)
        }
    }
    Impl(f1)
}

// pub fn adapt_both_sides(f : F) -> impl base::Tactic<Action>
// where F : Fn(&Func) -> Func {

// // crate::tactic![
// //     (&&
// //         (cut(func1))
// //         (cdr(cut(func2)))
// //         (cdr(swap()))
// //         (cdr(car(path::tactics::reverse())))
// //     )
// // ]
// }

pub fn double_cut(func1: &Func, func2: &Func) -> impl base::Tactic<Action> {
    crate::tactic![
        (&&(cut(func1))(cdr(cut(func2)))(cdr(swap()))(cdr(car(path::tactics::reverse()))))
    ]
}

pub fn simplify() -> impl base::Tactic<Action> {
    car(path::tactics::simplify())
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
    let one_side = || {
        crate::tactic![
            (&&(Cut())(car(path::tactics::induction()))(cdr(car(path::tactics::rec_z()))))
        ]
    };

    crate::tactic![
        (|| (one_side())(&&(car(path::tactics::reverse()))(one_side())(car(
            path::tactics::reverse()
        ))(cdr(car(path::tactics::reverse())))))
    ]
}

pub fn stack_split() -> impl base::Tactic<Action> {
    struct Cut();
    impl base::Tactic<Action> for Cut {
        fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
            let path::Path { start, end } = stack.head()?;
            let ((start_car, start_cdr), (end_car, end_cdr)) = (start.unstack()?, end.unstack()?);
            let mid = Func::stack(start_car, end_cdr).unwrap();
            apply_cut(&mid, stack)
        }
    }

    crate::tactic![
        (&&(Cut())(car(path::tactics::stack_cdr()))(cdr(car(path::tactics::stack_car()))))
    ]
}
