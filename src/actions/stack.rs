use crate::actions::path;
use crate::base;
use crate::func::Func;
use base::{Action as _, SyntaxEq};
use path::Path;
use std::fmt;

#[derive(Clone)]
pub enum Stack {
    Empty,
    Cons(Path, Box<Stack>),
}
impl Stack {
    fn iter(&self) -> Iter<'_> {
        Iter(self)
    }

    pub fn push(self, car: Path) -> Stack {
        Stack::Cons(car, Box::new(self))
    }

    pub fn snoc(self) -> Option<(Path, Stack)> {
        match self {
            Stack::Empty => None,
            Stack::Cons(car, cdr) => Some((car, *cdr)),
        }
    }
}

impl base::Point for Stack {}

pub struct Iter<'a>(&'a Stack);
impl<'a> Iterator for Iter<'a> {
    type Item = &'a path::Path;
    fn next(&mut self) -> Option<Self::Item> {
        match self.0 {
            Stack::Empty => None,
            Stack::Cons(car, cdr) => {
                self.0 = cdr;
                Some(car)
            }
        }
    }
}

impl fmt::Debug for Stack {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(head) = self.iter().next() {
            for _ in 0..self.iter().count() - 1 {
                fmt.write_str("  ")?
            }
            if fmt.alternate() {
                fmt.write_fmt(format_args!("{:#?} -> {:#?}", head.start, head.end))
            } else {
                fmt.write_fmt(format_args!("{:?} -> {:?}", head.start, head.end))
            }
        } else {
            fmt.write_str("EMPTY")
        }
    }
}

impl base::SyntaxEq for Stack {
    fn syntax_eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Stack::Empty, Stack::Empty) => true,
            (Stack::Empty, _) => false,
            (Stack::Cons(s_car, s_cdr), Stack::Cons(o_car, o_cdr)) => {
                s_car.syntax_eq(&*o_car) && s_cdr.syntax_eq(&*o_cdr)
            }
            (Stack::Cons(_, _), _) => false,
        }
    }
}

#[derive(Clone, Debug)]
pub enum Action {
    PushRefl(Func),
    HorizontalConcat,
    CarApply(path::Action),
    CdrApply(Box<Action>),
}

#[derive(Debug)]
pub enum Error {
    NotApplicable(Action),
}

impl Action {
    fn internal_act(&self, stack: Stack) -> Option<Stack> {
        match self {
            Action::PushRefl(f) => Some(stack.push(Path {
                start: f.clone(),
                end: f.clone(),
            })),
            Action::HorizontalConcat => {
                let (car, cdr) = stack.snoc()?;
                let (cdr_car, cdr_cdr) = cdr.snoc()?;
                if car.end.syntax_eq(&cdr_car.start) {
                    Some(cdr_cdr.push(Path {
                        start: car.start,
                        end: cdr_car.end,
                    }))
                } else {
                    None
                }
            }
            Action::CarApply(car_action) => {
                let (car, cdr) = stack.snoc()?;
                Some(cdr.push(car_action.act(car).ok()?))
            }
            Action::CdrApply(cdr_action) => {
                let (car, cdr) = stack.snoc()?;
                Some(cdr_action.act(cdr).ok()?.push(car))
            }
        }
    }
}

impl base::Action for Action {
    type Point = Stack;
    type Error = Error;
    fn act(&self, stack: Stack) -> Result<Stack, Error> {
        if let Some(res) = self.internal_act(stack) {
            Ok(res)
        } else {
            Err(Error::NotApplicable(self.clone()))
        }
    }
}

impl<P: base::Tactic<path::Action>> base::Tactic<Action> for P {
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

pub fn cdr<T:base::Tactic<Action>>(tactic: &T) -> impl base::Tactic<Action> {
    struct Impl<T:base::Tactic<Action>>(T);

impl<T:base::Tactic<Action>> base::Tactic<Action> for Impl<T> {
    fn react(&self, stack: &Stack) -> Option<base::ActionChain<Action>> {
        let (car, cdr) = stack.clone().snoc()?;
        let chain = self.react(&cdr)?;
        Some(base::ActionChain {
            start: chain.start.push(car),
            actions: chain
                .actions
                .into_iter()
                .map(|a| Action::CdrApply(a))
                .collect(),
        })
    }
    Impl(tactic)
}
