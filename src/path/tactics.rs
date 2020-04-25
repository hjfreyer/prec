use super::actions::*;
use super::*;
use crate::base;
use crate::base::SyntaxEq;
use crate::func::actions as fa;
use crate::func::tactics as ft;
use crate::tactic;

pub fn on_start<T: base::Tactic<fa::Action>>(tactic: T) -> impl base::Tactic<Action> {
    struct Impl<T: base::Tactic<fa::Action>>(T);
    impl<T: base::Tactic<fa::Action>> base::Tactic<Action> for Impl<T> {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let Self(tactic) = self;
            let chain = tactic.react(start)?;
            Some(base::ActionChain {
                start: Path {
                    start: chain.start,
                    end: end.clone(),
                },
                actions: chain
                    .actions
                    .into_iter()
                    .map(|a| Action::ActOnStart(a))
                    .collect(),
            })
        }
    }
    Impl(tactic)
}

pub fn on_end<T: base::Tactic<fa::Action>>(tactic: T) -> impl base::Tactic<Action> {
    struct Impl<T: base::Tactic<fa::Action>>(T);
    impl<T: base::Tactic<fa::Action>> base::Tactic<Action> for Impl<T> {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let Self(tactic) = self;
            let chain = tactic.react(end)?;
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
    Impl(tactic)
}

pub fn simplify() -> impl base::Tactic<Action> {
    tactic![(*(|| (on_start(ft::reduce_once())) (on_end(ft::reduce_once()))))]
}

pub fn induction() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start: f, end: rec }: &Path) -> Option<base::ActionChain<Action>> {
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

            Some(base::ActionChain {
                start: Path {
                    start: start_start,
                    end: start_end,
                },
                actions: im::vector![Action::Induction],
            })
        }
    }
    Impl()
}

pub fn reverse() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            Some (base::ActionChain{
                start: Path{start: end.clone(), end: start.clone()},
                actions: im::vector![Action::Reverse],
            })
        }
    }
    Impl()
}

pub fn rec_z() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let (start_z, start_s) = start.unrec()?;
            let (end_z, end_s) = end.unrec()?;
            if start_s.syntax_eq(&end_s) {
                Some(base::ActionChain {
                    start: Path {
                        start: start_z,
                        end: end_z,
                    },
                    actions: im::vector![Action::RecZ(start_s)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}

pub fn comp_left() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let ((start_f, start_g), (end_f, end_g)) = (start.decompose()?, end.decompose()?);
            println!("{:?} vs {:?}", start_g, end_g);
            if start_g.syntax_eq(&end_g) {
                Some(base::ActionChain {
                    start: Path {
                        start: start_f,
                        end: end_f,
                    },
                    actions: im::vector![Action::CompLeft(start_g)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}
