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

pub trait TypedPoint {
    type Type;
    type Path;
}

pub trait Transform<Point: TypedPoint> {
    fn input(&self) -> Point::Type;
    fn output(&self) -> Point::Type;
    fn apply(&self, start: &Point) -> Point::Path;
}

// pub trait Transform2 {
//     type Repr;
//     type Endpoint;

//     fn input(&self) -> Endpoint;
//     fn output(&self) -> Endpoint;
//     fn apply(&self, start: &Repr) -> Repr;
// }

pub trait Tactic<Point: TypedPoint> {
    type Transform: Transform<Point>;
    fn from_end(&self, end_type: &Point::Type) -> Option<Self::Transform>;
}
