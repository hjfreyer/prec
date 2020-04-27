pub mod actions;
pub mod tactics;

use crate::base;
use crate::func::Func;

#[derive(Clone, Debug)]
pub struct Path {
    pub start: Func,
    pub end: Func,
}

impl base::Point for Path {}
impl base::SyntaxEq for Path {
    fn syntax_eq(&self, other: &Self) -> bool {
        self.start.syntax_eq(&other.start) && self.end.syntax_eq(&other.end)
    }
}
