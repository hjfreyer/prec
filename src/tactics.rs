use crate::base;
use crate::base::{ActionChain, Tactic};

pub fn plus<A: base::Action, T: base::Tactic<A>>(tactic: T) -> impl base::Tactic<A> {
    struct Plus<A: base::Action, T: base::Tactic<A>>(T, std::marker::PhantomData<A>);

    impl<A: base::Action, T: base::Tactic<A>> Tactic<A> for Plus<A, T> {
        fn react(&self, p: &A::Point) -> Option<ActionChain<A>> {
            let Self(t, _) = self;
            let mut res = t.react(p)?;
            while let Some(mut ac) = t.react(&res.start) {
                std::mem::swap(&mut res, &mut ac);
                res.actions.append(ac.actions);
            }
            Some(res)
        }
    }
    Plus(tactic, std::marker::PhantomData)
}

pub fn star<A, T>(tactic: T) -> impl base::Tactic<A>
where
    A: base::Action,
    T: base::Tactic<A>,
    A::Point: Clone,
{
    struct Impl<A: base::Action, T: base::Tactic<A>>(T, std::marker::PhantomData<A>);

    impl<A: base::Action, T: base::Tactic<A>> Tactic<A> for Impl<A, T>
    where
        A::Point: Clone,
    {
        fn react(&self, p: &A::Point) -> Option<ActionChain<A>> {
            let Self(t, _) = self;
            if let Some(mut res) = t.react(p) {
                while let Some(mut ac) = t.react(&res.start) {
                    std::mem::swap(&mut res, &mut ac);
                    res.actions.append(ac.actions);
                }
                Some(res)
            } else {
                Some(ActionChain {
                    start: p.clone(),
                    actions: im::vector![],
                })
            }
        }
    }
    Impl(tactic, std::marker::PhantomData)
}

pub fn pipe<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(t1: T1, t2: T2) -> impl Tactic<A> {
    struct Pipe<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(T1, T2, std::marker::PhantomData<A>);
    impl<A: base::Action, T1: Tactic<A>, T2: Tactic<A>> Tactic<A> for Pipe<A, T1, T2> {
        fn react(&self, point: &A::Point) -> Option<ActionChain<A>> {
            let Self(t1, t2, _) = self;
            if let Some(chain1) = t1.react(&point) {
                if let Some(mut chain2) = t2.react(&chain1.start) {
                    chain2.actions.append(chain1.actions);
                    Some(chain2)
                } else {
                    Some(chain1)
                }
            } else {
                t2.react(&point)
            }
        }
    }
    Pipe(t1, t2, std::marker::PhantomData)
}

pub fn atomic_pipe<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(
    t1: T1,
    t2: T2,
) -> impl Tactic<A> {
    struct Pipe<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(T1, T2, std::marker::PhantomData<A>);
    impl<A: base::Action, T1: Tactic<A>, T2: Tactic<A>> Tactic<A> for Pipe<A, T1, T2> {
        fn react(&self, point: &A::Point) -> Option<ActionChain<A>> {
            let Self(t1, t2, _) = self;
            let chain1 = t1.react(&point)?;
            let mut chain2 = t2.react(&chain1.start)?;
            chain2.actions.append(chain1.actions);
            Some(chain2)
        }
    }
    Pipe(t1, t2, std::marker::PhantomData)
}

pub fn any<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(t1: T1, t2: T2) -> impl Tactic<A> {
    struct Impl<A: base::Action, T1: Tactic<A>, T2: Tactic<A>>(T1, T2, std::marker::PhantomData<A>);
    impl<A: base::Action, T1: Tactic<A>, T2: Tactic<A>> Tactic<A> for Impl<A, T1, T2> {
        fn react(&self, point: &A::Point) -> Option<ActionChain<A>> {
            let Self(t1, t2, _) = self;
            if let res @ Some(_) = t1.react(&point) {
                return res;
            }
            t2.react(&point)
        }
    }
    Impl(t1, t2, std::marker::PhantomData)
}

#[macro_export]
macro_rules! tactic {
    ((|| $head:tt $($tail:tt)+)) => {
        crate::tactics::any(crate::tactic![$head], crate::tactic![(|| $($tail)+)])
    };
    ((|| $head:tt )) => {       crate::tactic![$head]    };
    ((; $head:tt $($tail:tt)+)) => {
        crate::tactics::pipe(crate::tactic![$head], crate::tactic![(; $($tail)+)])
    };
    ((; $head:tt )) => {       crate::tactic![$head]    };
    ((&& $head:tt $($tail:tt)+)) => {
        crate::tactics::atomic_pipe(crate::tactic![$head], crate::tactic![(&& $($tail)+)])
    };
    ((&& $head:tt )) => {       crate::tactic![$head]    };
    ((* $f:tt)) => {
        crate::tactics::plus(crate::tactic![$f])
    };
    ($f:expr) => {$f};
}
