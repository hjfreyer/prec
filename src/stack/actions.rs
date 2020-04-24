use crate::base;
use crate::func::Func;
use crate::path;
use base::{Action as _, SyntaxEq};
use path::actions as pa;
use std::fmt;

use super::*;

#[derive(Clone, Debug)]
pub enum Action {
    PushRefl(Func),
    HorizontalConcat,
    CarApply(pa::Action),
    CdrApply(Box<Action>),
}

#[derive(Debug)]
pub enum Error {
    NotApplicable(Action),
}

impl Action {
    fn internal_act(&self, stack: Stack) -> Option<Stack> {
        match self {
            Action::PushRefl(f) => Some(stack.push(path::Path {
                start: f.clone(),
                end: f.clone(),
            })),
            Action::HorizontalConcat => {
                let (car, cdr) = stack.snoc()?;
                let (cdr_car, cdr_cdr) = cdr.snoc()?;
                if car.end.syntax_eq(&cdr_car.start) {
                    Some(cdr_cdr.push(path::Path {
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
