use crate::func;
use func::{Func, View as FView};

impl Func {
    pub fn decompose(&self) -> Option<(Func, Func)> {
        if let FView::Comp(f, g) = self.view() {
            Some((f.clone(), g.clone()))
        } else {
            None
        }
    }

    pub fn unstack(&self) -> Option<(Func, Func)> {
        if let FView::Stack(car, cdr) = self.view() {
            Some((car.clone(), cdr.clone()))
        } else {
            None
        }
    }

    pub fn unrec(&self) -> Option<(Func, Func)> {
        if let FView::Rec(z_case, s_case) = self.view() {
            Some((z_case.clone(), s_case.clone()))
        } else {
            None
        }
    }
}
