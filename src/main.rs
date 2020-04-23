#[macro_use]
mod func;
mod base;
mod metapath;
mod path;
mod pattern;
mod rewrite;
mod tactics;
use crate::base::{Endpoints, SyntaxEq};
use crate::func::{Func, View};
// use crate::rewrite::factory::Factory;
use crate::rewrite::Rewrite;
use im;
use im::vector::Vector;
use tactics::Tactic;



fn advance<M: tactics::Tactic>(g: tactics::Stack, m: M) -> tactics::Stack {
    let g = m.apply(&g).unwrap().0;
    println!("{:?}", g);
    g
}

fn main() {
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
    //    println!("{:#?}", is_even);

    //    let g = goal::HorizontalPath::new(func![(is_even double)], func![(const 1 (int 1))]);

    //    let mut g = im::vector![Endpoints(_t4, func![(int 1)])];

    // Proof that ed = 1

    let mut g =
        tactics::Stack::new().push(Endpoints(func![(is_even double)], func![(const 1 (int 1))]));
    println!("{:?}", g);

    g = advance(g, tactics::cut(&func![(rec (int 1) ((not not) (proj 0 2)))]));
    g = advance(g, tactics::induction());
    g = advance(g, tactics::auto());
    g = advance(g, tactics::auto());
    g = advance(g, path::reverse());
    g = advance(g, tactics::induction());
    g = advance(g, tactics::auto());
    g = advance(g, tactics::auto());
    // g = advance(g, rewrite::reduce_fully_tactic());
    // g = advance(g, tactics::refl());

    // g = advance(g, &tactics::InductionMatcher(func![((not not) (proj 0 2))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    // g = advance(g, &tactics::InductionMatcher(func![((not not) (proj 0 2))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::RecSplitMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    //    g = advance(g, &tactics::PushReflMatcher());

    // Proof that (half double) = id
    //
    // let mut g = tactics::ContextSpec::cons(
    //     Endpoints(func![(half double)], func![(proj 0 1)]),
    //     tactics::ContextSpec::Empty,
    // );
    // println!("{:?}", g);

    // g = advance(g, &tactics::InductionMatcher(func![(S (proj 0 2))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // let factored = func![((maybe_increment
    //     (not (proj 0 2))
    //     (maybe_increment
    //         (proj 0 2)
    //         (proj 1 2))) (not (is_even (double (proj 0 1)))) (half double))
    // ];
    // g = advance(g, &tactics::CutMatcher(factored));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());

    // let maybe_increment_gone = func![
    //     ((S (proj 1 2)) (not (is_even (double (proj 0 1)))) (half double))
    // ];
    // g = advance(g, &tactics::CutMatcher(maybe_increment_gone));
    // g = advance(g, &tactics::LiftMatcher(metapath::comp_left_match()));
    // g = advance(g, &tactics::InductionMatcher(func![(S (proj 2 3))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    // g = advance(g, &tactics::InductionMatcher(func![(S (proj 2 3))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::RecSplitMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    // g = advance(g, &tactics::InductionMatcher(func![(S (proj 0 2))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());

    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::RecSplitMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
}
