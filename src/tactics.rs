
use crate::base;
use crate::base::{ActionChain, Tactic};
use crate::func;
use func::Func;
//use im::vector::Vector;

use crate::actions::func::Action as FAction;
use crate::actions::path::{Action as PAction, Path};
use crate::actions::stack::{Action as SAction, Stack};
use crate::actions::stack;

pub struct Plus<A: base::Action, T: base::Tactic<A>>(T, std::marker::PhantomData<A>);

impl<A: base::Action, T: base::Tactic<A>> Tactic<A> for Plus<A, T> {
    fn react(&self, p: &A::Point) -> Option<ActionChain<A>> {
        let Self(t, _) = self;
        let mut res = t.react(p)?;
        while let Some(mut ac) = t.react(&res.start) {
            std::mem::swap(&mut res, &mut ac);
            res.actions.append(ac.actions);
        }
        Some(res)
    }
}

fn apply_cut(mid: &Func, stack: &Stack) -> Option<ActionChain<SAction>> {
    let (Path { start, end }, cdr) = stack.clone().snoc()?;
    let new_stack = cdr
        .push(Path {
            start: mid.clone(),
            end,
        })
        .push(Path {
            start,
            end: mid.clone(),
        });
    Some(ActionChain {
        start: new_stack,
        actions: im::vector![SAction::HorizontalConcat],
    })
}

pub fn cut(func: &Func) -> impl Tactic<SAction> {
    struct Impl(Func);
    impl Tactic<SAction> for Impl {
        fn react(&self, stack: &Stack) -> Option<ActionChain<SAction>> {
            let Self(mid) = self;
            apply_cut(mid, stack)
        }
    }
    Impl(func.clone())
}

// use crate::func;
// use crate::func::{BadFunc, Func, View as FView};
// use crate::path;
// use crate::path::{Action as PAction, View as PView};
// use crate::rewrite;
// use im::vector::Vector;
// use std::fmt;
// use std::mem;
// use std::rc::Rc;

// // use crate::metapath;
// // use metapath::{Matcher as MetapathMatcher, Metapath};

// #[derive(Clone, Debug)]
// pub enum StackActionView {
//     PushRefl(Func),
//     HorizontalConcat,
//     CarApply(PAction),
//     CdrApply(StackAction),
// }

// #[derive(Clone, Debug)]
// pub struct StackAction(Rc<StackActionView>);

// #[derive(Clone)]
// pub enum StackView {
//     Empty,
//     Cons(Endpoints<Func>, Stack),
// }

// #[derive(Clone)]
// pub struct Stack(Rc<StackView>);

// impl Stack {
//     pub fn new() -> Stack {
//         Stack(Rc::new(StackView::Empty))
//     }

//     pub fn push(self, car: Endpoints<Func>) -> Stack {
//         Stack(Rc::new(StackView::Cons(car, self)))
//     }

//     pub fn view(&self) -> &StackView {
//         &*self.0
//     }
//     pub fn head(&self) -> Option<Endpoints<Func>> {
//         match self.view() {
//             StackView::Empty => None,
//             StackView::Cons(car, _) => Some(car.clone()),
//         }
//     }
//     pub fn snoc(&self) -> Option<(Endpoints<Func>, Stack)> {
//         match self.view() {
//             StackView::Empty => None,
//             StackView::Cons(car, cdr) => Some((car.clone(), cdr.clone())),
//         }
//     }

//     pub fn iter(&self) -> EndpointsStackIntoIter {
//         self.clone().into_iter()
//     }
//     // pub fn endpoints(&self) -> EndpointsStack {
//     //     match self.view() {
//     //         StackView::Empty => EndpointsStack::new(),
//     //         StackView::Cons(car, cdr) => cdr.endpoints().push(car.endpoints()),
//     //     }
//     // }
// }

// impl fmt::Debug for Stack {
//     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
//         if let Some(head) = self.iter().next() {
//             for _ in (0..self.iter().count() - 1) {
//                 fmt.write_str("  ")?
//             }
//             if fmt.alternate() {
//                 fmt.write_fmt(format_args!("{:#?} -> {:#?}", head.start(), head.end()))
//             } else {
//                 fmt.write_fmt(format_args!("{:?} -> {:?}", head.start(), head.end()))
//             }
//         } else {
//             fmt.write_str("EMPTY")
//         }
//     }
// }

// impl IntoIterator for Stack {
//     type Item = Endpoints<Func>;
//     type IntoIter = EndpointsStackIntoIter;
//     fn into_iter(self) -> EndpointsStackIntoIter {
//         EndpointsStackIntoIter(self)
//     }
// }

// pub struct EndpointsStackIntoIter(Stack);
// impl Iterator for EndpointsStackIntoIter {
//     type Item = Endpoints<Func>;
//     fn next(&mut self) -> Option<Self::Item> {
//         match self.0.view().clone() {
//             StackView::Empty => None,
//             StackView::Cons(car, cdr) => {
//                 self.0 = cdr;
//                 Some(car)
//             }
//         }
//     }
// }

// pub trait Tactic {
//     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)>;
// }

// pub fn refl() -> impl Tactic {
//     struct Impl();
//     impl Tactic for Impl {
//         fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//             let (Endpoints(start, end), cdr) = stack.snoc()?;
//             if start.syntax_eq(&end) {
//                 Some((
//                     cdr,
//                     im::vector![StackAction(Rc::new(StackActionView::PushRefl(start)))],
//                 ))
//             } else {
//                 None
//             }
//         }
//     }
//     Impl()
// }

// // pub fn induction() -> impl Tactic {
// //     impl Tactic for () {
// //         fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
// //             let (Endpoints(start, end), cdr) = stack.snoc()?;

// //         }
// //     }
// // }

// struct CarTactic<T: path::Tactic>(T);

// impl<T: path::Tactic> Tactic for CarTactic<T> {
//     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//         let Self(pt) = self;
//         let (car, cdr) = stack.snoc()?;
//         let (eps, actions) = pt.apply(&car)?;
//         let new_stack = cdr.push(eps);
//         let new_actions = actions
//             .into_iter()
//             .map(|a| StackAction(Rc::new(StackActionView::CarApply(a))))
//             .collect();
//         Some((new_stack, new_actions))
//     }
// }

// struct CdrTactic<T: Tactic>(T);

// impl<T: Tactic> Tactic for CdrTactic<T> {
//     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//         let Self(t) = self;
//         let (car, cdr) = stack.snoc()?;
//         let (stack, actions) = t.apply(&cdr)?;
//         let new_stack = stack.push(car);
//         let new_actions = actions
//             .into_iter()
//             .map(|a| StackAction(Rc::new(StackActionView::CdrApply(a))))
//             .collect();
//         Some((new_stack, new_actions))
//     }
// }

// pub fn lift<T: path::Tactic>(t: T) -> impl Tactic {
//     CarTactic(t)
// }

struct Pipe<A : base::Action, T1: Tactic<A>, T2: Tactic<A>>(T1, T2, std::marker::PhantomData<A>);
impl<A : base::Action, T1: Tactic<A>, T2: Tactic<A>> Tactic<A> for Pipe<A, T1, T2> {
    fn react(&self, point: &A::Point) -> Option<ActionChain<A>> {
        let Self(t1, t2, _) = self;
        let chain1 = t1.react(&point)?;
        let mut chain2 = t2.react(&chain1.start)?;
        chain2.actions.append(chain1.actions);
Some(chain2)
    }
}

pub fn induction() -> impl Tactic {
    struct Cut();
    impl Tactic for Cut {
        fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
            let Endpoints(f, rec) = stack.head()?;
            let (z_case, s_case) = rec.unrec()?;
            let f_arity = f.arity().r#in;
            let mid = Func::rec(Func::comp(f, Func::z_eye(f_arity)).unwrap(), s_case).unwrap();
            apply_cut(&mid, stack)
        }
    }
    Pipe(
        Cut(),
        Pipe(path::induction(), stack::cdr(path::rec_z())),
    )

    // struct Impl();
    // impl Tactic for Impl {
    //     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {

    //     }
    // }
    // Impl();
}

// struct TryTactic<T: Tactic>(T);
// impl<T: Tactic> Tactic for TryTactic<T> {
//     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//         let Self(t) = self;
//         if let res @ Some(_) = t.apply(stack) {
//             res
//         } else {
//             Some((stack.clone(), im::vector![]))
//         }
//     }
// }

// pub fn simplify() -> impl Tactic {
//     ComposeTactics(
//         TryTactic(rewrite::reduce_fully_tactic()),
//         ComposeTactics(
//             path::reverse(),
//             ComposeTactics(TryTactic(rewrite::reduce_fully_tactic()), path::reverse()),
//         ),
//     )
//     // struct Impl();
//     // impl Tactic for Impl {
//     //     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//     //         let (Endpoints(start, end), cdr) = stack.snoc()?;
//     //         if start.syntax_eq(&end) {
//     //             Some((cdr, im::vector![StackAction(Rc::new(StackActionView::PushRefl(start)))]))
//     //         } else {
//     //             None
//     //         }
//     //     }
//     // }
//     // Impl()
// }

// pub fn auto() -> impl Tactic {
//     ComposeTactics(simplify(), TryTactic(refl()))
//     // struct Impl();
//     // impl Tactic for Impl {
//     //     fn apply(&self, stack: &Stack) -> Option<(Stack, Vector<StackAction>)> {
//     //         let (Endpoints(start, end), cdr) = stack.snoc()?;
//     //         if start.syntax_eq(&end) {
//     //             Some((cdr, im::vector![StackAction(Rc::new(StackActionView::PushRefl(start)))]))
//     //         } else {
//     //             None
//     //         }
//     //     }
//     // }
//     // Impl()
// }

// // pub struct Induction(metapath::Induction, Func, ContextSpec);

// // impl MetaMultipath for Induction {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(ind, target, ctx) = self;
// //         let Endpoints(Endpoints(f_s, s_applied), Endpoints(f, rec)) = ind.endpoints();
// //         Endpoints(
// //             ContextSpec::cons(
// //                 Endpoints(f_s.clone(), s_applied.clone()),
// //                 ContextSpec::cons(Endpoints(rec.clone(), target.clone()), ctx.clone()),
// //             ),
// //             ContextSpec::cons(Endpoints(f.clone(), target.clone()), ctx.clone()),
// //         )
// //     }
// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }
// // pub struct InductionMatcher(pub Func);

// // impl MetaMultipathMatcher for InductionMatcher {
// //     type MMP = Induction;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         let InductionMatcher(s_case) = self;
// //         if let ContextSpec::Cons(Endpoints(f, target), cdr) = end {
// //             return Some(Induction(
// //                 metapath::Induction(f.clone(), s_case.clone()),
// //                 target.clone(),
// //                 (**cdr).clone(),
// //             ));
// //         }
// //         None
// //     }
// // }

// // // trait Tactic3 {
// // //     fn step_backwards(&self, eps : EndpointsStack) -> Option<(EndpointsStack, Vector<StackAction>)>
// // // }

// // // pub trait Transform0 {
// // //     fn endpoints(&self) -> Endpoints<Func>;
// // //     fn apply(&self, start: &Func) -> Path;
// // // }

// // // pub trait Transform1 {
// // //     fn endpoints(&self) -> Endpoints<Endpoints<Func>>;
// // //     fn apply(&self, start: &Path) -> Path;
// // // }

// // // pub trait Transform2 {
// // //     fn endpoints(&self) -> Endpoints<EndpointsStack>;
// // //     fn apply(&self, start: &Stack) -> Stack;
// // // }

// // // struct CompLeftTransform1(Transform0)

// // // pub enum Metapath2 {

// // // }

// // // impl SyntaxEq for Stack {
// // //     fn syntax_eq(&self, other: &Self) -> bool {
// // //         match (self.view(), other.view()) {
// // //             (StackView::Empty, StackView::Empty) => true,
// // //             (StackView::Empty, _) => false,
// // //             (StackView::Cons(s_car, s_cdr), StackView::Cons(o_car, o_cdr)) => {
// // //                 s_car.syntax_eq(o_car) && s_cdr.syntax_eq(o_cdr)
// // //             }
// // //             (StackView::Cons(_, _), _) => false,
// // //         }
// // //     }
// // // }

// // // impl TypedPoint for Stack {
// // //     type Type = EndpointsStack;
// // // }

// // // #[derive(Clone)]
// // // pub enum EndpointsStackView {
// // //     Empty,
// // //     Cons(Endpoints<Func>, EndpointsStack),
// // // }

// // // #[derive(Clone)]
// // // pub struct EndpointsStack(Rc<EndpointsStackView>);

// // // impl EndpointsStack {
// // //     pub fn new() -> EndpointsStack {
// // //         EndpointsStack(Rc::new(EndpointsStackView::Empty))
// // //     }

// // //     pub fn push(self, car: Endpoints<Func>) -> EndpointsStack {
// // //         EndpointsStack(Rc::new(EndpointsStackView::Cons(car, self)))
// // //     }

// // //     pub fn view(&self) -> &EndpointsStackView {
// // //         &*self.0
// // //     }

// // //     pub fn iter(&self) -> EndpointsStackIntoIter {
// // //         self.clone().into_iter()
// // //     }

// // //     pub fn snoc(&self) -> Option<(Endpoints<Func>, EndpointsStack)> {
// // //         match self.view() {
// // //             EndpointsStackView::Empty => None,
// // //             EndpointsStackView::Cons(car, cdr) => Some((car.clone(), cdr.clone())),
// // //         }
// // //     }
// // // }

// // // impl SyntaxEq for EndpointsStack {
// // //     fn syntax_eq(&self, other: &Self) -> bool {
// // //         match (self.view(), other.view()) {
// // //             (EndpointsStackView::Empty, EndpointsStackView::Empty) => true,
// // //             (EndpointsStackView::Empty, _) => false,
// // //             (EndpointsStackView::Cons(s_car, s_cdr), EndpointsStackView::Cons(o_car, o_cdr)) => {
// // //                 s_car.syntax_eq(o_car) && s_cdr.syntax_eq(o_cdr)
// // //             }
// // //             (EndpointsStackView::Cons(_, _), _) => false,
// // //         }
// // //     }
// // // }

// // // struct ConsTransform(Path, EndpointsStack);

// // // impl Transform<Stack> for ConsTransform {
// // //     fn input(&self) -> EndpointsStack {
// // //         let Self(_, cdr) = self;
// // //         cdr.clone()
// // //     }

// // //     fn output(&self) -> EndpointsStack {
// // //         let Self(car, cdr) = self;
// // //         cdr.clone().push(car.endpoints())
// // //     }

// // //     fn apply(&self, input: &Stack) -> Stack {
// // //         let Self(car, _) = self;
// // //         input.clone().push(car.clone())
// // //     }
// // // }

// // // pub trait Breaker<Point: TypedPoint> {
// // //     type PointA: TypedPoint;
// // //     type PointB: TypedPoint;

// // //     fn break_point(t: &Point) -> (Self::PointA, Self::PointB);
// // //     fn weld_point(a: &Self::PointA, b: &Self::PointB) -> Point;
// // //     fn break_type(
// // //         t: &Point::Type,
// // //     ) -> (
// // //         <Self::PointA as TypedPoint>::Type,
// // //         <Self::PointB as TypedPoint>::Type,
// // //     );
// // //     fn weld_type(
// // //         a: &<Self::PointA as TypedPoint>::Type,
// // //         b: &<Self::PointB as TypedPoint>::Type,
// // //     ) -> (Point::Type);
// // // }

// // // struct CarBreaker();

// // // impl Breaker<Stack> for CarBreaker {
// // //     type PointA = Path;
// // //     type PointB = Stack;

// // //     fn break_point(t: &Stack) -> (Path, Stack) {
// // //         t.clone().snoc().unwrap()
// // //     }
// // //     fn weld_point(a: &Path, b: &Stack) -> Stack {
// // //         b.clone().push(a.clone())
// // //     }
// // //     fn break_type(t: &EndpointsStack) -> (Endpoints<Func>, EndpointsStack) {
// // //         t.clone().snoc().unwrap()
// // //     }
// // //     fn weld_type(a: &Endpoints<Func>, b: &EndpointsStack) -> EndpointsStack {
// // //         b.clone().push(a.clone())
// // //     }
// // // }
// // // struct CdrBreaker();

// // // impl Breaker<Stack> for CdrBreaker {
// // //     type PointA = Stack;
// // //     type PointB = Path;

// // //     fn break_point(t: &Stack) -> (Stack, Path) {
// // //         let (car, cdr) = t.clone().snoc().unwrap();
// // //         (cdr, car)
// // //     }
// // //     fn weld_point(a: &Stack, b: &Path) -> Stack {
// // //         a.clone().push(b.clone())
// // //     }
// // //     fn break_type(t: &EndpointsStack) -> (EndpointsStack, Endpoints<Func>) {
// // //         let (car, cdr) = t.clone().snoc().unwrap();
// // //         (cdr, car)
// // //     }
// // //     fn weld_type(a: &EndpointsStack, b: &Endpoints<Func>) -> EndpointsStack {
// // //         a.clone().push(b.clone())
// // //     }
// // // }

// // // struct StructuralTransform<P: TypedPoint, B: Breaker<P>, AT: Transform<B::PointA>>(
// // //     AT,
// // //     <B::PointB as TypedPoint>::Type,
// // //     std::marker::PhantomData<P>,
// // //     std::marker::PhantomData<B>,
// // // );

// // // impl<Point: TypedPoint, B: Breaker<Point>, PT: Transform<B::PointA>> Transform<Point>
// // //     for StructuralTransform<Point, B, PT>
// // // {
// // //     fn input(&self) -> Point::Type {
// // //         let Self(at, b, _, _) = self;
// // //         B::weld_type(&at.input(), b)
// // //     }

// // //     fn output(&self) -> Point::Type {
// // //         let Self(at, b, _, _) = self;
// // //         B::weld_type(&at.output(), b)
// // //     }

// // //     fn apply(&self, input: &Point) -> Point {
// // //         let Self(at, _, _, _) = self;
// // //         let (a, b) = B::break_point(input);
// // //         B::weld_point(&at.apply(&a), &b)
// // //     }
// // // }

// // // type CarTransform<T> = StructuralTransform<Stack, CarBreaker, T>;
// // // type CdrTransform<T> = StructuralTransform<Stack, CdrBreaker, T>;

// // // pub fn car_tactic<PT: Tactic<Path>>(tactic: PT) -> impl Tactic<Stack> {
// // //     struct Impl<PT2: Tactic<Path>>(PT2);

// // //     impl<PT2: Tactic<Path>> Tactic<Stack> for Impl<PT2> {
// // //         type Transform = CarTransform<PT2::Transform>;
// // //         fn from_end(&self, end_type: &EndpointsStack) -> Option<Self::Transform> {
// // //             let Self(path_tactic) = self;
// // //             let (car, cdr) = end_type.snoc()?;
// // //             let path_trans = path_tactic.from_end(&car)?;
// // //             Some(StructuralTransform(
// // //                 path_trans,
// // //                 cdr,
// // //                 std::marker::PhantomData,
// // //                 std::marker::PhantomData,
// // //             ))
// // //         }
// // //     }

// // //     Impl(tactic)
// // // }

// // // pub fn cdr_tactic<PT: Tactic<Stack>>(tactic: PT) -> impl Tactic<Stack> {
// // //     struct Impl<PT: Tactic<Stack>>(PT);

// // //     impl<PT: Tactic<Stack>> Tactic<Stack> for Impl<PT> {
// // //         type Transform = CdrTransform<PT::Transform>;
// // //         fn from_end(&self, end_type: &EndpointsStack) -> Option<Self::Transform> {
// // //             let Self(cdr_tactic) = self;
// // //             let (car, cdr) = end_type.snoc()?;
// // //             let cdr_trans = cdr_tactic.from_end(&cdr)?;
// // //             Some(StructuralTransform(
// // //                 cdr_trans,
// // //                 car,
// // //                 std::marker::PhantomData,
// // //                 std::marker::PhantomData,
// // //             ))
// // //         }
// // //     }

// // //     Impl(tactic)
// // // }

// // // struct CdrBreaker();

// // // impl Breaker<Stack, Stack, Path,  EndpointsStack, Endpoints<Func>> for CdrBreaker {
// // //     fn break_point(t : Stack) -> (Stack, Path) {
// // //         let (car, cdr) = t.snoc().unwrap();
// // //         (cdr, car)
// // //         }
// // //     fn weld_point(a : Stack, b : Path) -> Stack {a.push(b)}
// // //     fn break_type(t : EndpointsStack) -> (EndpointsStack, Endpoints<Func>) {        let (car, cdr) = t.snoc().unwrap();
// // //         (cdr, car) }
// // //     fn weld_type(a:EndpointsStack, b:Endpoints<Func>) -> EndpointsStack {a.push(b)}
// // // }

// // // pub trait Breaker<Point : TypedPoint, PointA, PointB, TypeA, TypeB> {
// // //     fn break_point(t : Point) -> (PointA, PointB);
// // //     fn weld_point(a : PointA, b : PointB) -> Point;
// // //     fn break_type(t : Point::Type) -> (TypeA, TypeB);
// // //     fn weld_type(a : TypeA, b : TypeB) -> Point::Type;
// // // }

// // // struct CarBreaker();

// // // impl Breaker<Stack, Path, Stack, Endpoints<Func>, EndpointsStack> for CarBreaker {
// // //     fn break_point(t : Stack) -> (Path, Stack) { t.snoc().unwrap() }
// // //     fn weld_point(a : Path, b : Stack) -> Stack {b.push(a)}
// // //     fn break_type(t : EndpointsStack) -> (Endpoints<Func>, EndpointsStack) {t.snoc().unwrap()}
// // //     fn weld_type(a : Endpoints<Func>, b : EndpointsStack) -> EndpointsStack {b.push(a)}
// // // }

// // // struct CdrBreaker();

// // // impl Breaker<Stack, Stack, Path,  EndpointsStack, Endpoints<Func>> for CdrBreaker {
// // //     fn break_point(t : Stack) -> (Stack, Path) {
// // //         let (car, cdr) = t.snoc().unwrap();
// // //         (cdr, car)
// // //         }
// // //     fn weld_point(a : Stack, b : Path) -> Stack {a.push(b)}
// // //     fn break_type(t : EndpointsStack) -> (EndpointsStack, Endpoints<Func>) {        let (car, cdr) = t.snoc().unwrap();
// // //         (cdr, car) }
// // //     fn weld_type(a:EndpointsStack, b:Endpoints<Func>) -> EndpointsStack {a.push(b)}
// // // }

// // // struct CarTransform<PT: Transform<Path>>(PT, EndpointsStack);

// // // impl<PT: Transform<Path>> Transform<Stack> for CarTransform<PT> {
// // //     fn input(&self) -> EndpointsStack {
// // //         let Self(car_t, cdr) = self;
// // //         cdr.clone().push(car_t.input())
// // //     }

// // //     fn output(&self) -> EndpointsStack {
// // //         let Self(car_t, cdr) = self;
// // //         cdr.clone().push(car_t.output())
// // //     }

// // //     fn apply(self, input: Stack) -> Stack {
// // //         let Self(car_t, _) = self;
// // //         let (car, cdr) = input.snoc().unwrap();
// // //         cdr.push(car_t.apply(car))
// // //     }
// // // }

// // // struct PushPathTransform<T : Tactic<Path>>(Path, EndpointsStack);

// // // impl <T : Tactic<Path>> Transform<Stack> for PushPathTransform<T> {
// // //     fn input(&self) -> EndpointsStack {
// // //         let Self(_, cdr) = self;
// // //         cdr.clone()
// // //     }

// // //     fn output(&self) -> EndpointsStack {
// // //         let Self(car, cdr) = self;
// // //         cdr.clone().push(car.endpoints())
// // //     }

// // //     fn apply(self, input : Stack) -> Stack {
// // //         let Self(car, _) = self;
// // //         input.push(car)
// // //     }
// // // }

// // // pub struct PushReflMatcher();

// // // impl MetaMultipathMatcher for PushReflMatcher {
// // //     type MMP = PushRefl;
// // //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// // //         if let ContextSpec::Cons(Endpoints(start, end), cdr) = end {
// // //             if start.syntax_eq(end) {
// // //                 return Some(PushRefl(start.clone(), (**cdr).clone()));
// // //             }
// // //         }
// // //         None
// // //     }
// // // }

// // pub enum Context {
// //     Empty,
// //     Cons(Path, Rc<Context>),
// // }

// // #[derive(Clone)]
// // pub enum ContextSpec {
// //     Empty,
// //     Cons(Endpoints<Func>, Rc<ContextSpec>),
// // }

// // impl ContextSpec {
// //     pub fn iter(&self) -> ContextSpecIntoIter {
// //         self.clone().into_iter()
// //     }

// //     pub fn cons(car: Endpoints<Func>, cdr: ContextSpec) -> Self {
// //         Self::Cons(car, Rc::new(cdr))
// //     }
// // }

// // impl IntoIterator for ContextSpec {
// //     type Item = Endpoints<Func>;
// //     type IntoIter = ContextSpecIntoIter;
// //     fn into_iter(self) -> ContextSpecIntoIter {
// //         ContextSpecIntoIter(self)
// //     }
// // }

// // pub struct ContextSpecIntoIter(ContextSpec);
// // impl Iterator for ContextSpecIntoIter {
// //     type Item = Endpoints<Func>;
// //     fn next(&mut self) -> Option<Self::Item> {
// //         match self.0.clone() {
// //             ContextSpec::Empty => None,
// //             ContextSpec::Cons(car, cdr) => {
// //                 self.0 = (*cdr).clone();
// //                 Some(car)
// //             }
// //         }
// //     }
// // }

// // impl SyntaxEq for ContextSpec {
// //     fn syntax_eq(&self, other: &Self) -> bool {
// //         match (self, other) {
// //             (ContextSpec::Empty, ContextSpec::Empty) => true,
// //             (ContextSpec::Empty, _) => false,
// //             (ContextSpec::Cons(s_car, s_cdr), ContextSpec::Cons(o_car, o_cdr)) => {
// //                 s_car.syntax_eq(o_car) && s_cdr.syntax_eq(o_cdr)
// //             }
// //             (ContextSpec::Cons(_, _), _) => false,
// //         }
// //     }
// // }
// // impl fmt::Debug for ContextSpec {
// //     fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
// //         for _ in (0..self.iter().count() - 1) {
// //             fmt.write_str("  ")?
// //         }
// //         if let Some(head) = self.iter().next() {
// //             fmt.write_fmt(format_args!("{:?} -> {:?}", head.start(), head.end()))?;
// //         }
// //         Ok(())
// //     }
// // }

// // pub trait MetaMultipath {
// //     fn endpoints(&self) -> Endpoints<ContextSpec>;
// //     fn unchecked_apply(&self, start: &Context) -> Context;
// // }

// // pub trait MetaMultipathMatcher {
// //     type MMP: MetaMultipath;
// //     fn match_start(&self, start: &ContextSpec) -> Option<Self::MMP> {
// //         unimplemented!()
// //     }

// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         unimplemented!()
// //     }
// // }

// // pub struct PushRefl(Func, ContextSpec);

// // impl MetaMultipath for PushRefl {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let PushRefl(f, ctx) = self;
// //         Endpoints(
// //             ctx.clone(),
// //             ContextSpec::cons(Endpoints(f.clone(), f.clone()), ctx.clone()),
// //         )
// //     }

// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }

// // pub struct PushReflMatcher();

// // impl MetaMultipathMatcher for PushReflMatcher {
// //     type MMP = PushRefl;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         if let ContextSpec::Cons(Endpoints(start, end), cdr) = end {
// //             if start.syntax_eq(end) {
// //                 return Some(PushRefl(start.clone(), (**cdr).clone()));
// //             }
// //         }
// //         None
// //     }
// // }

// // pub struct Cut(pub Func, pub Func, pub Func, pub ContextSpec);

// // impl MetaMultipath for Cut {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(a, b, c, ctx) = self;
// //         Endpoints(
// //             ContextSpec::cons(
// //                 Endpoints(a.clone(), b.clone()),
// //                 ContextSpec::cons(Endpoints(b.clone(), c.clone()), ctx.clone()),
// //             ),
// //             ContextSpec::cons(Endpoints(a.clone(), c.clone()), ctx.clone()),
// //         )
// //     }

// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }

// // pub struct CutMatcher(pub Func);

// // impl MetaMultipathMatcher for CutMatcher {
// //     type MMP = Cut;
// //     fn match_end(&self, end_path: &ContextSpec) -> Option<Self::MMP> {
// //         let CutMatcher(mid) = self;
// //         if let ContextSpec::Cons(Endpoints(start, end), cdr) = end_path {
// //             return Some(Cut(
// //                 start.clone(),
// //                 mid.clone(),
// //                 end.clone(),
// //                 (**cdr).clone(),
// //             ));
// //         }
// //         None
// //     }
// // }

// // pub struct Concat<MMP1: MetaMultipath, MMP2: MetaMultipath>(pub MMP1, pub MMP2);

// // impl<MMP1: MetaMultipath, MMP2: MetaMultipath> MetaMultipath for Concat<MMP1, MMP2> {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(p1, p2) = self;
// //         Endpoints(p1.endpoints().start().clone(), p2.endpoints().end().clone())
// //     }

// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }
// // pub struct ConcatMatcher<MMPM1: MetaMultipathMatcher, MMPM2: MetaMultipathMatcher>(
// //     pub MMPM1,
// //     pub MMPM2,
// // );

// // impl<MMPM1: MetaMultipathMatcher, MMPM2: MetaMultipathMatcher> MetaMultipathMatcher
// //     for ConcatMatcher<MMPM1, MMPM2>
// // {
// //     type MMP = Concat<MMPM1::MMP, MMPM2::MMP>;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         let ConcatMatcher(m1, m2) = self;
// //         if let Some(p2) = m2.match_end(end) {
// //             let mid = p2.endpoints().start().clone();
// //             if let Some(p1) = m1.match_end(&mid) {
// //                 return Some(Concat(p1, p2));
// //             }
// //         }
// //         None
// //     }
// // }

// // pub struct Lift<MP: Metapath>(MP, ContextSpec);

// // impl<MP: Metapath> MetaMultipath for Lift<MP> {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(mp, ctx) = self;
// //         let Endpoints(start, end) = mp.endpoints();
// //         Endpoints(
// //             ContextSpec::cons(start, ctx.clone()),
// //             ContextSpec::cons(end, ctx.clone()),
// //         )
// //     }
// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }
// // pub struct LiftMatcher<MPM: MetapathMatcher>(pub MPM);

// // impl<MPM: MetapathMatcher> MetaMultipathMatcher for LiftMatcher<MPM> {
// //     type MMP = Lift<MPM::MP>;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         let LiftMatcher(lift_matcher) = self;
// //         if let ContextSpec::Cons(ep, cdr) = end {
// //             if let Some(m) = lift_matcher.match_end(ep) {
// //                 return Some(Lift(m, (**cdr).clone()));
// //             }
// //         }
// //         None
// //     }
// // }

// // pub struct Lift2<MP: Metapath>(Endpoints<Func>, MP, ContextSpec);

// // impl<MP: Metapath> MetaMultipath for Lift2<MP> {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(head, mp, ctx) = self;
// //         let Endpoints(start, end) = mp.endpoints();
// //         Endpoints(
// //             ContextSpec::cons(head.clone(), ContextSpec::cons(start, ctx.clone())),
// //             ContextSpec::cons(head.clone(), ContextSpec::cons(end, ctx.clone())),
// //         )
// //     }
// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }
// // pub struct Lift2Matcher<MPM: MetapathMatcher + ?Sized>(pub MPM);

// // impl<MPM: MetapathMatcher + ?Sized> MetaMultipathMatcher for Lift2Matcher<MPM> {
// //     type MMP = Lift2<MPM::MP>;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         let Self(lift_matcher) = self;
// //         if let ContextSpec::Cons(head, cdr) = end {
// //             if let ContextSpec::Cons(ep, cdr) = &**cdr {
// //                 if let Some(m) = lift_matcher.match_end(ep) {
// //                     return Some(Lift2(head.clone(), m, (**cdr).clone()));
// //                 }
// //             }
// //         }
// //         None
// //     }
// // }

// // pub struct Induction(metapath::Induction, Func, ContextSpec);

// // impl MetaMultipath for Induction {
// //     fn endpoints(&self) -> Endpoints<ContextSpec> {
// //         let Self(ind, target, ctx) = self;
// //         let Endpoints(Endpoints(f_s, s_applied), Endpoints(f, rec)) = ind.endpoints();
// //         Endpoints(
// //             ContextSpec::cons(
// //                 Endpoints(f_s.clone(), s_applied.clone()),
// //                 ContextSpec::cons(Endpoints(rec.clone(), target.clone()), ctx.clone()),
// //             ),
// //             ContextSpec::cons(Endpoints(f.clone(), target.clone()), ctx.clone()),
// //         )
// //     }
// //     fn unchecked_apply(&self, start: &Context) -> Context {
// //         unimplemented!()
// //     }
// // }
// // pub struct InductionMatcher(pub Func);

// // impl MetaMultipathMatcher for InductionMatcher {
// //     type MMP = Induction;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         let InductionMatcher(s_case) = self;
// //         if let ContextSpec::Cons(Endpoints(f, target), cdr) = end {
// //             return Some(Induction(
// //                 metapath::Induction(f.clone(), s_case.clone()),
// //                 target.clone(),
// //                 (**cdr).clone(),
// //             ));
// //         }
// //         None
// //     }
// // }

// // pub struct RecCutMatcher();

// // impl MetaMultipathMatcher for RecCutMatcher {
// //     type MMP = Cut;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         if let ContextSpec::Cons(Endpoints(start_rec, end_rec), cdr) = end {
// //             if let (FView::Rec(start_z, start_s), FView::Rec(end_z, end_s)) =
// //                 (start_rec.view(), end_rec.view())
// //             {
// //                 let midpoint = Func::rec(end_z.clone(), start_s.clone()).unwrap();
// //                 return CutMatcher(midpoint).match_end(end);
// //             }
// //         }
// //         None
// //     }
// // }

// // pub struct RecSplitMatcher();

// // impl MetaMultipathMatcher for RecSplitMatcher {
// //     type MMP = Concat<Lift<metapath::RecZ>, Concat<Lift2<metapath::RecS>, Cut>>;
// //     fn match_end(&self, end: &ContextSpec) -> Option<Self::MMP> {
// //         ConcatMatcher(
// //             LiftMatcher(metapath::RecZMatcher()),
// //             ConcatMatcher(Lift2Matcher(metapath::RecSMatcher()), RecCutMatcher()),
// //         )
// //         .match_end(end)
// //     }
// // }
