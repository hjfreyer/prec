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
    tactic![(*(|| (on_start(ft::reduce_once()))(on_end(ft::reduce_once()))))]
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
            Some(base::ActionChain {
                start: Path {
                    start: end.clone(),
                    end: start.clone(),
                },
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

pub fn comp_right() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let ((start_f, start_g), (end_f, end_g)) = (start.decompose()?, end.decompose()?);
            if start_f.syntax_eq(&end_f) {
                Some(base::ActionChain {
                    start: Path {
                        start: start_g,
                        end: end_g,
                    },
                    actions: im::vector![Action::CompRight(start_f)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}

pub fn stack_car() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let ((start_car, start_cdr), (end_car, end_cdr)) = (start.unstack()?, end.unstack()?);
            if start_cdr.syntax_eq(&end_cdr) {
                Some(base::ActionChain {
                    start: Path {
                        start: start_car,
                        end: end_car,
                    },
                    actions: im::vector![Action::StackCar(start_cdr)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}

pub fn stack_cdr() -> impl base::Tactic<Action> {
    struct Impl();
    impl base::Tactic<Action> for Impl {
        fn react(&self, Path { start, end }: &Path) -> Option<base::ActionChain<Action>> {
            let ((start_car, start_cdr), (end_car, end_cdr)) = (start.unstack()?, end.unstack()?);
            if start_car.syntax_eq(&end_car) {
                Some(base::ActionChain {
                    start: Path {
                        start: start_cdr,
                        end: end_cdr,
                    },
                    actions: im::vector![Action::StackCdr(start_car)],
                })
            } else {
                None
            }
        }
    }
    Impl()
}
