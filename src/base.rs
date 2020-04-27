use std::fmt::Debug;

pub trait SyntaxEq {
    fn syntax_eq(&self, other: &Self) -> bool;
}

pub trait Point: SyntaxEq + Debug {}

pub trait Action: Clone {
    type Point: Point;
    type Error: Debug;
    fn act(&self, point: Self::Point) -> Result<Self::Point, Self::Error>;
}

#[derive(Debug)]
pub struct ActionChain<A: Action> {
    pub start: A::Point,
    pub actions: im::Vector<A>,
}

pub trait Tactic<A: Action> {
    fn react(&self, p: &A::Point) -> Option<ActionChain<A>>;
}
