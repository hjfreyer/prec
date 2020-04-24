use std::fmt::Debug;

pub trait SyntaxEq {
    fn syntax_eq(&self, other: &Self) -> bool;
}

#[derive(Clone, Debug)]
pub struct Endpoints<T: SyntaxEq>(pub T, pub T);

impl<T: SyntaxEq> Endpoints<T> {
    pub fn start(&self) -> &T {
        &self.0
    }

    pub fn end(&self) -> &T {
        &self.1
    }
}

impl<T: SyntaxEq> SyntaxEq for Endpoints<T> {
    fn syntax_eq(&self, other: &Self) -> bool {
        self.start().syntax_eq(other.start()) && self.end().syntax_eq(other.end())
    }
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
    //    end: A::Point,
    pub actions: im::Vector<A>,
}

// pub enum ExtensionError<A: Action> {
//     EndpointsMisaligned(ActionChain<A>, ActionChain<A>),
// }

// impl<A: Action> ActionChain<A> {
//     pub fn new(point: A::Point) -> ActionChain<A> {
//         ActionChain {
//             start: point,
//   //          end: point,
//             actions: im::vector![],
//         }
//     }

//     pub fn push_front()

//     pub fn extend(&mut self, other: Self) -> Result<(), ExtensionError<A>> {
//         if !self.end().syntax_eq(other.start()) {
//             return Err(ExtensionError::EndpointsMisaligned(self, other));
//         }
//         self.actions.extend(other.actions);
//         Ok(Self {
//             start: self.start,
//             end: other.end,
//             actions: self.actions,
//         })
//     }

//     pub fn start(&self) -> &A::Point {
//         &self.start
//     }

//     pub fn end(&self) -> &A::Point {
//         &self.end
//     }
// }

pub trait Tactic<A: Action> {
    fn react(&self, p: &A::Point) -> Option<ActionChain<A>>;
}
