use crate::base::{Endpoints, SyntaxEq};
use crate::func;
use crate::pattern;
use crate::rewrite;
use crate::rewrite::Rewrite;
use func::View as FView;
use func::{BadFunc, Func};
use std::rc::Rc;

#[derive(Clone, Debug)]
pub struct Path(Rc<View>);

#[derive(Clone, Debug)]
pub enum View {
    Refl(Func),
    Reverse(Path),
    Concat(Path, Path),

    Rewrite(Rewrite),

    // Induction.
    Induction(Func, Func, Path),

    // Steps in nested structures.
    CompLeft(Path, Func),
    CompRight(Func, Path),
    StackCar(Path, Func),
    StackCdr(Func, Path),
    RecZ(Path, Func),
    RecS(Func, Path),
}

#[derive(Clone, Debug)]
pub enum BadPath {
    IncompatibleArity(Func, Func),
}

impl Path {
    pub fn validate(view: View) -> Result<Path, BadPath> {
        // TODO: Validate.
        Ok(Path(Rc::new(view)))
    }

    pub fn endpoints(&self) -> Endpoints<Func> {
        match &*self.0 {
            View::Refl(f) => Endpoints(f.clone(), f.clone()),
            View::Reverse(p) => {
                let Endpoints(start, end) = p.endpoints();
                Endpoints(end, start)
            }
            View::Concat(left, right) => Endpoints(
                left.endpoints().start().clone(),
                right.endpoints().end().clone(),
            ),

            View::Rewrite(rw) => rw.endpoints(),

            View::Induction(f, s_case, _) => Endpoints(
                f.clone(),
                Func::rec(
                    Func::comp(f.clone(), Func::z_eye(f.arity().r#in())).unwrap(),
                    s_case.clone(),
                )
                .unwrap(),
            ),

            View::CompLeft(f_rw, g) => Endpoints(
                Func::comp(f_rw.endpoints().start().clone(), g.clone()).unwrap(),
                Func::comp(f_rw.endpoints().end().clone(), g.clone()).unwrap(),
            ),
            View::CompRight(f, g_rw) => Endpoints(
                Func::comp(f.clone(), g_rw.endpoints().start().clone()).unwrap(),
                Func::comp(f.clone(), g_rw.endpoints().end().clone()).unwrap(),
            ),
            View::StackCar(car_rw, cdr) => Endpoints(
                Func::stack(car_rw.endpoints().start().clone(), cdr.clone()).unwrap(),
                Func::stack(car_rw.endpoints().end().clone(), cdr.clone()).unwrap(),
            ),
            View::StackCdr(car, cdr_rw) => Endpoints(
                Func::stack(car.clone(), cdr_rw.endpoints().start().clone()).unwrap(),
                Func::stack(car.clone(), cdr_rw.endpoints().end().clone()).unwrap(),
            ),
            View::RecZ(z_rw, s_case) => Endpoints(
                Func::rec(z_rw.endpoints().start().clone(), s_case.clone()).unwrap(),
                Func::rec(z_rw.endpoints().end().clone(), s_case.clone()).unwrap(),
            ),
            View::RecS(z_case, s_rw) => Endpoints(
                Func::rec(z_case.clone(), s_rw.endpoints().start().clone()).unwrap(),
                Func::rec(z_case.clone(), s_rw.endpoints().end().clone()).unwrap(),
            ),
        }
    }
}

pub trait PathFinder {
    fn match_start(&self, func: &Func) -> Option<Path>;
}

pub struct Reducer();

impl PathFinder for Reducer {
    fn match_start(&self, func: &Func) -> Option<Path> {
        Some(reduce_fully(func))
    }
}


// fn factor() -> impl PathFinder {
//     struct Impl();

// impl PathFinder for Impl {
//     fn match_start(&self, func: &Func) -> Option<Path> {
//         rewrite::comp_factor_stack()(func)
//         let Self(factored) = self;
//         let proposal = Path::validate(View::Reverse(Rewrite::validate(RView::CompDistributeEmpty(factored)).unwrap())).unwrap();
//         if proposal.endpoints().start().syntax_eq(func) {
//             Some(proposal)
//         } else {
//             None
//         }
//     }
// }
// Impl()
// }



pub fn reduce_once(func: &Func) -> Option<Path> {
    macro_rules !try_rules {
        ($($rule:ident),*) => {
            None
            $(.or_else(|| rewrite::Rule::$rule.match_start(func)))*
        }
    }

    let rw_reduction = try_rules!(
        ProjCar,
        ProjCdr,
        ProjCar,
        ProjCdr,
        RecElimZ,
        RecElimS,
        EtaReductionLeft,
        EtaReductionRight,
        CompAssoc,
        CompDistributeEmpty,
        CompDistributeStack
    );
    if let Some(rw) = rw_reduction {
        return Some(Path::validate(View::Rewrite(rw)).unwrap());
    }

    if let FView::Comp(f, g) = func.view() {
        let opt = None
            .or_else(|| {
                reduce_once(f).map(|rw| Path::validate(View::CompLeft(rw, g.clone())).unwrap())
            })
            .or_else(|| {
                reduce_once(g).map(|rw| Path::validate(View::CompRight(f.clone(), rw)).unwrap())
            });
        if let Some(p) = opt {
            return Some(p);
        }
    }
    if let FView::Stack(car, cdr) = func.view() {
        let opt = None
            .or_else(|| {
                reduce_once(car).map(|rw| Path::validate(View::StackCar(rw, cdr.clone())).unwrap())
            })
            .or_else(|| {
                reduce_once(cdr).map(|rw| Path::validate(View::StackCdr(car.clone(), rw)).unwrap())
            });
        if let Some(p) = opt {
            return Some(p);
        }
    }

    None
}

// Returns a path starting with f and leading to a reduced form.
pub fn reduce_fully(func: &Func) -> Path {
    let mut res = Path::validate(View::Refl(func.clone())).unwrap();

    while let Some(ext) = reduce_once(res.endpoints().end()) {
        res = Path::validate(View::Concat(res, ext)).unwrap();
    }
    res
}
