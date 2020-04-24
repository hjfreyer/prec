pub mod actions;
pub mod tactics;

use crate::base;
use crate::path;
use std::fmt;

#[derive(Clone)]
pub enum Stack {
    Empty,
    Cons(path::Path, Box<Stack>),
}
impl Stack {
    fn iter(&self) -> Iter<'_> {
        Iter(self)
    }

    pub fn push(self, car: path::Path) -> Stack {
        Stack::Cons(car, Box::new(self))
    }

    pub fn snoc(self) -> Option<(path::Path, Stack)> {
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
