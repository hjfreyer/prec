#[macro_use]
use crate::func;
use func::{Func, View as FView};

pub fn add_free_variable(func: Func) -> Func {
    fn checked(func: Func) -> Result<Func, func::BadFunc> {

    // match func.into_view() {
    //     FView::Z => 
    //         Func::mk_const(1, Func::z()).unwrap(),
    //     FView::S => 
    //         Func::apply(Func::s(), &[Func::proj(0, 2).unwrap()]).unwrap(),
    //     FView::Proj(select, arity) => Func::proj(select, arity + 1).unwrap(),
    //     FView::Empty(arity) => Func::stack(
    //         Func::proj(arity, arity + 1).unwrap(),
    //         Func::empty(arity + 1),
    //     )
    //     .unwrap(),
    //     FView::Stack(car, cdr) => {
    //         Func::stack(add_free_variable(car), add_free_variable(cdr)).unwrap()
    //     }
    //     FView::Comp(f, g) => Func::comp(add_free_variable(f), add_free_variable(g)).unwrap(),
    //     FView::Rec(z_case, s_case) => {
    //         Func::rec(add_free_variable(z_case), add_free_variable(s_case)).unwrap()
    //     }
    // }

    // version that increases out arity
    match func.into_view() {
        FView::Z => Func::stack(
            Func::mk_const(1, Func::z())?,
            Func::stack(Func::proj(0, 1)?, Func::empty(1))?
        ),
        FView::S => Func::stack(
            Func::apply(Func::s(), &[Func::proj(0, 2)?])?,
            Func::stack(Func::proj(1, 2)?, Func::empty(2))?),
        FView::Proj(select, arity) =>  Func::stack(
            Func::proj(select, arity + 1)?,
            Func::stack(Func::proj(arity, arity+1)?, Func::empty(arity+1))?),
        FView::Empty(arity) => Func::stack(
            Func::proj(arity, arity + 1)?,
            Func::empty(arity + 1),
        ),
        FView::Stack(car, cdr) => {
            let car = Func::comp(Func::proj(0, 2)?, checked(car)?)?;
            Func::stack(car, checked(cdr)?)
        }
        FView::Comp(f, g) => Func::comp(checked(f)?, checked(g)?),
        FView::Rec(z_case, s_case) => {
            let z_arity = z_case.arity().r#in;
            let z_case = Func::comp(Func::proj(0, 2)?, checked(z_case)?)?;
            let s_case = Func::comp(Func::proj(0, 2)?, checked(s_case)?)?;
            
            Func::stack(
                Func::rec(z_case, s_case)?,
                Func::stack(Func::proj(z_arity + 1, z_arity + 2)?, Func::empty(z_arity + 2))?
            )
        }
    }
    }
checked(func).unwrap()

    // func
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn it_works() {
        func_let![
            let _a = ((proj 2 3) (int 0) (int 1) (int 2));
            let _t1 = ((const 3 Z) (int 0) (int 1) (int 2));
            let _t2 = ((const 3 Z) (const 2 (int 0)) (const 2 (int 1)) (const 2 (int 2)));
            let _t3 = (((proj 0 2) (proj 1 3) (proj 0 3)) (int 0) (int 1) (int 2));
            let not = (rec (int 1) (const 2 Z));


            let _t4 = (not Z);
            let _t5 = (not S);
            let _t6 = (not (const 5 Z));
            let _t7 = (not (not (const 1 (int 5))));
            let _b = ((proj 2 3) (const 0 (int 1)) (int 2) (int 3));

            let is_even = (rec (int 1) (not (proj 0 2)));
            let double = (rec (int 0) (S (S (proj 0 2))));

            let maybe_increment = (rec (proj 0 1) (S (proj 2 3)));
            let plus_mod2 = (maybe_increment (not (is_even (proj 0 2))) (proj 1 2));
            let half = (rec (int 0) (plus_mod2 (proj 1 2) (proj 0 2)));
        ];
        add_free_variable(double);
        assert_eq!(2 + 2, 4);
    }
}
