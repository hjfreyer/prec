// #[macro_use]
pub mod base;
pub mod func;
pub mod path;
pub mod stack;
// mod func_manipulation;
// mod metapath;
// mod path;
// mod pattern;
// mod rewrite;
pub mod tactics;
// use crate::base::{Endpoints, SyntaxEq};
// use crate::func::{Func, View};
// // use crate::rewrite::factory::Factory;
// use crate::rewrite::Rewrite;
// use im;
// use im::vector::Vector;
// use tactics::Tactic;
use base::Tactic;
use stack::Stack;
// fn advance<M: tactics::Tactic>(g: tactics::Stack, m: M) -> tactics::Stack {
//     let g = m.apply(&g).unwrap().0;
//     println!("{:?}", g);
//     g
// }

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
        let _double = (rec (int 0) (S (S (proj 0 2))));

        let maybe_increment = (rec (proj 0 1) (S (proj 2 3)));
        let plus_mod2 = (maybe_increment (not (is_even (proj 0 2))) (proj 1 2));
        let _half = (rec (int 0) (plus_mod2 (proj 1 2) (proj 0 2)));
    ];

    macro_rules! solve {
            ($a:expr, $b: expr; $($tactic:expr;)*) => {
                {
                    let mut stack = Stack::Empty.push(path::Path{start: $a, end: $b});
                    println!("{:?}", stack);
                    $(
                        {
                            let chain = $tactic.react(&stack).unwrap();
                            stack = chain.start;
                            println!("{:?}", stack);
                        }
                    )*
                    stack
                }
            }
        }

    // Proof that ed = 1

    // let factored = func![((maybe_increment
    //     (not (proj 0 2))
    //     (maybe_increment
    //         (proj 0 2)
    //         (proj 1 2))) (not (is_even (_double (proj 0 1)))) (_half _double))
    // ];
    // let factored2 = func![((S
    //         (proj 1 2)) (not (is_even (_double (proj 0 1)))) (_half _double))
    // ];

    // let _stack = solve!(
    //     func![(_half _double)], func![(proj 0 1)];
    //     stack::tactics::cut(&func![(rec (int 0) (S (proj 0 2)))]);
    //     stack::tactics::induction();
    //     //stack::tactics::car(path::tactics::simplify());
    //     // stack::tactics::auto();
    //     stack::tactics::cut(&factored2);
    //     stack::tactics::cut(&factored);
    //     stack::tactics::turbo();
    //     stack::tactics::car(path::tactics::comp_left());
    //     stack::tactics::cut(&func![(rec (S (proj 0 1)) (S (proj 2 3)))]);
    //     stack::tactics::turbo();
    // );

    func_let![
        let _add = (rec (proj 0 1) (S (proj 0 3)));
        let _const2 = ((int 2) * (!2));
        let _swap = [(proj 1 2), (proj 0 2)];
    ];
    //     // Proof that addition is commutataive.
    //     solve!(
    //             func![_add], func![ (_add * _swap)];
    //             stack::tactics::induction();
    //             stack::tactics::cut(&func![((S _add) * _swap)]);
    //             stack::tactics::auto();
    //             stack::tactics::car(path::tactics::reverse());
    //             stack::tactics::cut(&func![((_add * _swap *(s_i 2) * _swap) * _swap)]);
    //             stack::tactics::auto();
    //             stack::tactics::car(path::tactics::reverse());
    //             stack::tactics::car(path::tactics::comp_left());
    //             stack::tactics::cut(&func![(rec S (S (proj 0 3)))]);
    //             stack::tactics::turbo();
    //             stack::tactics::cut(&func![(rec (int 0) (S (proj 0 2)))]);
    //             stack::tactics::turbo();
    //     );
    //  println!("NEXT");

    // Proof that addition is associative.
    // solve!(
    //     func![(_add (_add (proj 0 3) (proj 1 3)) (proj 2 3))],
    //     func![(_add (proj 0 3) (_add (proj 1 3) (proj 2 3)))];
    //     stack::tactics::cut(&func![(rec _add (S (proj 0 4)))]);
    //     stack::tactics::turbo();
    // );

    func_let![
        let _pred = (rec (int 0) (proj 1 2));
        let _sub = (rec
            (proj 0 1)
            (_pred (proj 0 3))
        );
        let _eq_zero = (rec (int 1) (const 2 (int 0)));
        let _bor = (rec (proj 0 1) (const 3 (int 1)));
    ];

    // solve!(
    //         func![_sub],
    //         func![(_sub (S (proj 0 2)) (S (proj 1 2)))];
    //         // stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
    //         // stack::tactics::cut(&func![(rec
    //         //     (const 1 (int 1))
    //         //     ((rec (const 1 (int 1)) (proj 0 3))
    //         //         (proj 2 3)
    //         //         (proj 1 3)
    //         //     )
    //         // )
    //     //     // ]);
    //         // stack::tactics::turbo();
    //     //     stack::tactics::apply_and_cut(|f| func![((f * _swap) * _swap)]);
    //     //     stack::tactics::auto();
    //     //     stack::tactics::auto();
    //     //     stack::tactics::car(path::tactics::comp_left());
    //     //    stack::tactics::simplify();
    //     //     stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
    //     //     stack::tactics::induction();
    //     //    stack::tactics::simplify();
    //     //     stack::tactics::apply_and_cut(|f| func![((f * _swap) * _swap)]);
    //     //     stack::tactics::auto();
    //     //     stack::tactics::auto();
    //     //     stack::tactics::car(path::tactics::comp_left());
    //     );
    solve!(
        func![((_bor (_eq_zero _sub) (_eq_zero * [_sub] * _swap)) * [(proj 0 2), _add])],
        func![(const 2 (int 1))];
        stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
        // stack::tactics::cut(&func![(rec
        //     (const 1 (int 1))
        //     ((rec (const 1 (int 1)) (proj 0 3))
        //         (proj 2 3)
        //         (proj 1 3)
        //     )
        // )
    //     // ]);
        stack::tactics::induction();
        stack::tactics::simplify();
        stack::tactics::car(path::tactics::comp_right());
        stack::tactics::stack_split();
        stack::tactics::stack_split();
        stack::tactics::refl();
        stack::tactics::car(path::tactics::comp_right());
        stack::tactics::car(path::tactics::stack_car());
    //      stack::tactics::cut(&func![_sub]);
    //     stack::tactics::induction();
    //    stack::tactics::simplify();
    //     stack::tactics::apply_and_cut(|f| func![((f * _swap) * _swap)]);
    //     stack::tactics::auto();
    //     stack::tactics::auto();
    //    stack::tactics::simplify();
    //     stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
    //     stack::tactics::induction();
    //    stack::tactics::simplify();
    //     stack::tactics::apply_and_cut(|f| func![((f * _swap) * _swap)]);
    //     stack::tactics::auto();
    //     stack::tactics::auto();
    //     stack::tactics::car(path::tactics::comp_left());
    );

    // solve!(
    //       func![((_bor (_eq_zero _sub) (_eq_zero * [_sub] * _swap)) * [(S (proj 0 2)), (S (proj 1 2))]
    //       )],
    //     func![(const 2 (int 1))];
    //     stack::tactics::simplify();
    //     // stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
    //     // stack::tactics::induction();
    //     // stack::tactics::apply_and_cut(|f| func![((f * _swap) * _swap)]);
    //     // stack::tactics::auto();
    //     // stack::tactics::auto();
    //     // stack::tactics::car(path::tactics::comp_left());
    //     // stack::tactics::cut(&func![(rec (const 1 (int 1)) (proj 0 3))]);
    //     // stack::tactics::induction();
    //     // stack::tactics::simplify();
    // );

    //     //
    //     let (stack, actions) = solve!(
    //             tactics::cut(&func![(rec (int 0) (S (proj 0 2)))]);
    //             tactics::induction();
    //             rewrite::reduce_fully_tactic();
    //             path::reverse();
    //             rewrite::reduce2();
    //     //        rewrite::reduce_fully_tactic();
    //         // rewrite::Rule::CompAssocLeft;
    //     //        rewrite::reduce_n_times(10);
    //         //     tactics::simplify();

    //         );

    //     // let augmented = func_manipulation::add_free_variable(func![(half double)])
    //     //     .set_tag(func::Tag::Alias("augmented"));
    //     // let (stack, actions) = solve!(func![(augmented (proj 0 1) (const 1 (int 0)))], func![(half double)];
    //     //     tactics::simplify();
    //     //     // tactics::refl();
    //     // );

    //     // let steps = rewrite::reduce(
    //     //     &func![(comp (proj 0 2) ((augmented (proj 0 1) (const 1 (int 0))) (int 1)))],
    //     // );
    //     // let steps = rewrite::reduce_fully(
    //     //     &func![((half double) (S (proj 0 1)))]);

    //     // // // println!("{:?}", steps.head().unwrap().endpoints().start());
    //     // // // println!("{:?}", steps.last().unwrap().endpoints().end());
    //     // for step in steps {
    //     //     // println!("{:?}", step);
    //     //     println!("{:?}", step.endpoints().end());
    //     //     // println!();
    //     // }

    //     // g = advance(g, &tactics::InductionMatcher(func![(S (proj 0 2))]));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // let factored = func![((maybe_increment
    //     //     (not (proj 0 2))
    //     //     (maybe_increment
    //     //         (proj 0 2)
    //     //         (proj 1 2))) (not (is_even (double (proj 0 1)))) (half double))
    //     // ];
    //     // g = advance(g, &tactics::CutMatcher(factored));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());

    //     // let maybe_increment_gone = func![
    //     //     ((S (proj 1 2)) (not (is_even (double (proj 0 1)))) (half double))
    //     // ];
    //     // g = advance(g, &tactics::CutMatcher(maybe_increment_gone));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::comp_left_match()));
    //     // g = advance(g, &tactics::InductionMatcher(func![(S (proj 2 3))]));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());
    //     // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    //     // g = advance(g, &tactics::InductionMatcher(func![(S (proj 2 3))]));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());
    //     // g = advance(g, &tactics::RecSplitMatcher());
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());
    //     // g = advance(g, &tactics::PushReflMatcher());
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());
    //     // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    //     // g = advance(g, &tactics::InductionMatcher(func![(S (proj 0 2))]));
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());

    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::RecSplitMatcher());
    //     // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    //     // g = advance(g, &tactics::PushReflMatcher());
}
