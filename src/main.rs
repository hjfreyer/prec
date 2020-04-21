#[macro_use]
mod func;
mod base;
mod metapath;
mod path;
mod rewrite;
mod tactics;
use crate::base::{Endpoints, SyntaxEq};
use crate::func::{Func, View};
// use crate::rewrite::factory::Factory;
use crate::rewrite::Rewrite;
use im;
use im::vector::Vector;
use tactics::{MetaMultipath, MetaMultipathMatcher};

fn advance<M: tactics::MetaMultipathMatcher>(
    g: tactics::ContextSpec,
    m: &M,
) -> tactics::ContextSpec {
    let g = m.match_end(&g).unwrap().endpoints().start().clone();
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

    let mut g = tactics::ContextSpec::cons(
        Endpoints(func![(is_even double)], func![(const 1 (int 1))]),
        tactics::ContextSpec::Empty,
    );
    println!("{:?}", g);

    g = advance(g, &tactics::InductionMatcher(func![((not not) (proj 0 2))]));
    g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    g = advance(g, &tactics::PushReflMatcher());
    g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    g = advance(g, &tactics::InductionMatcher(func![((not not) (proj 0 2))]));
    g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    g = advance(g, &tactics::PushReflMatcher());
    g = advance(g, &tactics::RecSplitMatcher());
    g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    g = advance(g, &tactics::PushReflMatcher());
    g = advance(g, &tactics::PushReflMatcher());

    // let mut g = tactics::ContextSpec::cons(
    //     Endpoints(func![(half double)], func![(proj 0 1)]),
    //     tactics::ContextSpec::Empty,
    // );
    // println!("{:?}", g);

    // g = advance(g, &tactics::InductionMatcher(func![(S (proj 0 2))]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));

    // g = advance(g, &tactics::InductionMatcher(func![(proj 0 2)]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());
    // g = advance(g, &tactics::LiftMatcher(metapath::ReverseMatcher()));
    // g = advance(g, &tactics::InductionMatcher(func![(proj 0 2)]));
    // g = advance(g, &tactics::LiftMatcher(metapath::SimplifyMatcher()));
    // g = advance(g, &tactics::PushReflMatcher());

    //     let tax : Vec<Box<dyn tactics::MetaMultipathMatcher>>= vec![
    // //        &tactics::PushReflMatcher(),
    //  //   Box::new(tactics::LiftMatcher(Box::new(metapath::SimplifyMatcher())))
    //         // &tactics::Simplify(),
    //         //       tactics::forward_chain::<tactics::PushRefl>,
    // //        tactics::forward_chain::<tactics::Symm>,
    //         Box::new(tactics::InductionMatcher(func![((not not) (proj 0 2))])),
    //  Box::new(tactics::LiftMatcher(Box::new(metapath::SimplifyMatcher()))),
    //  Box::new(tactics::PushReflMatcher()),
    //  Box::new(tactics::LiftMatcher(Box::new(metapath::ReverseMatcher()))),
    //         Box::new(tactics::InductionMatcher(func![(proj 0 2)])),
    //  Box::new(tactics::LiftMatcher(Box::new(metapath::SimplifyMatcher()))),
    //  Box::new(tactics::PushReflMatcher()),
    // //  Box::new(tactics::LiftMatcher(Box::new(metapath::SimplifyMatcher()))),
    // // Box::new(tactics::PushReflMatcher()),
    //         // Box::new(tactics::CutMatcher(func![(rec (int 1) ((not not) (proj 0 2)))])),
    //         // Box::new(tactics::LiftMatcher(Box::new(metapath::SimplifyMatcher()))),
    //         //       tactics::Tactic::Induction(func![((not not) (proj 0 2))]),
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::Tactic::Symm,
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::Tactic::Ident,
    //         // tactics::Tactic::Symm,
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::Tactic::Induction(func![(proj 0 2)]),
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::Tactic::Symm,
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::Tactic::Ident,
    //         // tactics::Tactic::ReduceRight,
    //         // tactics::ContextTransformFactoryFamily::PushRefl,
    //     ];
    //     println!("{:?}", g);
    //     for t in tax.into_iter() {
    //         g = t.match_end(&g).unwrap().endpoints().start().clone();
    //         println!("{:?}", g);
    //         // for op in t.for_goal(&g) {
    //         //     g = op.reverse(g.clone()).unwrap();
    //         //     println!("{:?}", tactics::ContextSpecWrapper(g.clone()));
    //         // }
    //     }

    // println!("got here");
    // println!("{:?}", g);

    // let mut expr = _t7;
    // println!("{:?}", expr);
    // while let Some(rw) = rewrite::factory::Reduce().for_lhs(expr.clone()) {
    //     println!("{:?}", rw);

    //     if !expr.syntax_eq(&rw.clone().lhs()) {
    //         println!("wanted to match:   {:#?}", expr);
    //         println!("reduction was for: {:#?}", &rw.clone().lhs());
    //         panic!("ya done goofed")
    //     }
    //     expr = rw.rhs();
    //     println!("{:?}", expr);
    // }
    // let reduction = std::iter::successors(Some(_t6), |a| {
    //     rewrite::factory::Reduce()
    //         .for_lhs(a.clone())
    //         .map(|rw| {println!("{:?}", rw); rw.rhs()})
    // }).take(100);
    // for r in reduction {
    //     println!("{:?}", r)
    // }

    // let mut g = tactics::Goal::Active(tactics::Endpoints(func![(is_even double)], func![(const 1 (int 1))]));
    // println!("{:?}", g);
    // g.apply(tactics::Factory::Rewrite(rewrite::Factory::CompAssocFwd));
    // println!("{:?}", g);
    // let ca = rewrite::RuleFamily::match_side(rewrite::RuleFamily::CompAssoc,
    //     rewrite::Side::Left, &_a).unwrap().rhs();
    // let ca = rewrite::RuleFamily::match_side(rewrite::RuleFamily::CompAssoc,
    //     rewrite::Side::Left, &ca).unwrap().rhs();
    // println!("{:?}", ca)
    // if let View::Comp(f, g) = ca.image().view() {
    //     println!("{:?}", g);
    //     let gg = rewrite::SkipStack::from_preimage(g).unwrap().image();
    //     println!("{:?}", gg);
    // }
    // let z1 = func::View::Z;
    // let z2 = func::View::Z;

    // let s1 = func::View::Stack(&z1, &z1);
    // let s2 = func::View::Stack(&z2, &z2);

    // println!("{}", s1 == s2)
    //     define_prec![

    //

    //                 let double = (rec (int 0) (S (S (proj 0 2))));
    //                 let maybe_increment = (rec (proj 0 1) (S (proj 2 3)));
    //     //            let plus_mod2 = (rec (int 0) (not (proj 0 2)));

    //                 let mod2 = (rec (int 0) (not (proj 0 2)));
    //                 let plus_mod2 = (maybe_increment (not (is_even (proj 0 2))) (proj 1 2));
    //                 let half = (rec (int 0) (plus_mod2 (proj 1 2) (proj 0 2)));

    //                 let hd = (half double);
    //                 let ident = (proj 0 1);
    //                 let hd_scase = (S (proj 0 2));

    //         //        let half = (rec (int 0) )
    //                 let bl = (rec Z (const 2 (int 1)));
    //                 let ed = (is_even double);
    //                 let edz = (ed (const 0 Z));
    //                 let eds = (ed (S (proj 0 1)));

    //                 let zcase = (int 1);
    //                 let scase = (not (not (proj 0 2)));
    //                 let scase_applied = (scase ed (proj 0 1));

    //                 let nn = (not not);
    //                 let nns = (nn S);

    //                 let bl = (rec Z (const 2 (int 1)));

    //                 let one = (const 1 (int 1));
    //                 let one_zcase = (int 1);
    //                 let one_scase = (const 2 (int 1));

    //                 let maybe_or_not_increment = (maybe_increment (not (proj 0 2)) (maybe_increment (proj 0 2) (proj 1 2)));
    //                 let increment_arg1 = (S (proj 1 2));
    //                 let rec_bridge = (rec S (S (proj 2 3)));

    //                 let factored = (maybe_or_not_increment (not (is_even double)) (half double));
    //             ];

    //     println!(
    //         "{:?}",
    //         Goal::new(ed.clone(), prec![(const 1 (int 1))])
    //             .unwrap()
    //             .induction(prec![((not not) (proj 0 2))])
    //             .auto()
    //             .swap()
    //             .induction(prec![((not not) (proj 0 2))])
    //             .auto()
    //             .rec()
    //             // .simplify()
    //             // .swap()
    //             // .simplify()
    //             // .swap()
    //             .auto() //            .auto()

    //                     //  .auto()
    //                     // .auto()
    //                     //            .rec()
    //                     //        .cut(prec![(rec Z )])

    //                     //           .induction(prec![((not not) (proj 0 2))])
    //                     // .auto()
    //                     // .swap()
    //                     // .induction(prec![((not not) (proj 0 2))])
    //                     // .auto()
    //                     // .auto() //        .auto()
    //                     //     .cut(factored.clone())
    //                     //     .auto()
    //                     //        .simplify()
    //     );
}

// (((int 0) * !2) * <((rec (int 1) ((int 0) * !2)) * (stack (proj 0 1) (empty 1))); (stack (proj 0 1) (empty 1))>)

// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp S (stack (proj 0 1) (empty 1)))
//         (empty 1)))

// (comp (comp Z (empty 2))
//     (stack
//         (comp (rec (comp S (stack Z (empty 0))) (comp Z (empty 2))) (stack (stack (proj 0 1) (empty 1)) (empty 1)))
//         (stack (stack (proj 0 1) (empty 1)) (empty 1))))

// wanted to match:
// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp
//             (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//             (stack
//                 (comp S (stack (comp (comp S (stack (comp S (stack (comp S (stack (comp S (stack Z (empty 0))) (empty 0))) (empty 0))) (empty 0))) (empty 1)) (comp (empty 0) (empty 1))))
//                 (empty 1)))
//         (empty 1)))

// reduction was for:
// (comp
//     (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//     (stack
//         (comp
//             (rec (comp S (stack Z (empty 0))) (comp Z (empty 2)))
//             (stack
//                 (comp S (stack (comp (comp S (stack (comp S (stack (comp S (stack (comp S (stack Z (empty 0))) (empty 0))) (empty 0))) (empty 0))) (empty 1)) (empty 1)))
//                 (empty 1)))
//     (empty 1)))
