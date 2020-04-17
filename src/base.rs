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
