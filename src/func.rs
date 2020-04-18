use crate::base::SyntaxEq;
use itertools::Itertools;
use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum View {
    // Base functions.
    Z,
    S,

    // Projection functions.
    Proj(u32, u32),

    // Stacking functions.
    Empty(u32),
    Stack(Func, Func),

    // Combinators.
    Comp(Func, Func),
    Rec(Func, Func),
}

#[derive(Clone)]
pub struct Func(Rc<View>, Tag);

#[derive(Debug)]
pub struct Arity(pub u32, pub u32);

impl Arity {
    pub fn out(&self) -> u32 {
        self.0
    }
    pub fn r#in(&self) -> u32 {
        self.1
    }
}

#[derive(Debug, Clone)]
pub enum Tag {
    None,
    Alias(&'static str),
}

#[derive(Debug)]
pub enum BadFunc {
    InvalidProjection(u32, u32),
    StackCarOutArityMustBe1(Func),
    StackArityMismatch(Func, Func),
    CompArityMismatch(Func, Func),
    CompRightMustBeCompOrStack(Func, Func),
    RecZCaseOutArityMustBe1(Func),
    RecSCaseOutArityMustBe1(Func),
    RecArityMismatch(Func, Func),
}

impl Func {
    // Constructors.
    pub fn z() -> Func {
        Func(Rc::new(View::Z), Tag::None)
    }

    pub fn s() -> Func {
        Func(Rc::new(View::S), Tag::None)
    }

    pub fn proj(select: u32, arity: u32) -> Result<Func, BadFunc> {
        if arity <= select {
            return Err(BadFunc::InvalidProjection(select, arity));
        }
        Ok(Func(Rc::new(View::Proj(select, arity)), Tag::None))
    }

    pub fn empty(arity_in: u32) -> Func {
        Func(Rc::new(View::Empty(arity_in)), Tag::None)
    }

    pub fn stack(car: Func, cdr: Func) -> Result<Func, BadFunc> {
        let Arity(car_out, car_in) = car.arity();
        let Arity(_, cdr_in) = cdr.arity();

        if car_out != 1 {
            return Err(BadFunc::StackCarOutArityMustBe1(car));
        }
        if car_in != cdr_in {
            return Err(BadFunc::StackArityMismatch(car, cdr));
        }

        Ok(Func(Rc::new(View::Stack(car, cdr)), Tag::None))
    }

    pub fn comp(f: Func, g: Func) -> Result<Func, BadFunc> {
        match g.view() {
            View::Empty(_) | View::Stack(_, _) | View::Comp(_, _) => (),
            _ => return Err(BadFunc::CompRightMustBeCompOrStack(f, g)),
        }

        let Arity(_f_out, f_in) = f.arity();
        let Arity(g_out, _g_in) = g.arity();
        if f_in != g_out {
            Err(BadFunc::CompArityMismatch(f, g))
        } else {
            Ok(Func(Rc::new(View::Comp(f, g)), Tag::None))
        }
    }

    pub fn rec(z_case: Func, s_case: Func) -> Result<Func, BadFunc> {
        let Arity(z_out, z_in) = z_case.arity();
        let Arity(s_out, s_in) = s_case.arity();
        if z_out != 1 {
            return Err(BadFunc::RecZCaseOutArityMustBe1(z_case));
        }
        if s_out != 1 {
            return Err(BadFunc::RecSCaseOutArityMustBe1(s_case));
        }
        if z_in + 2 != s_in {
            return Err(BadFunc::RecArityMismatch(z_case, s_case));
        }

        Ok(Func(Rc::new(View::Rec(z_case, s_case)), Tag::None))
    }

    // Helper constructors.
    pub fn int(value: u32) -> Func {
        let mut res = Func::z();
        for ii in 0..value {
            res = Func::apply(Func::s(), &[res]).unwrap();
        }
        res
    }

    pub fn mk_const(arity: u32, f: Func) -> Result<Func, BadFunc> {
        Func::comp(f.clone(), Func::empty(arity))
    }

    pub fn apply(f: Func, gs: &[Func]) -> Result<Func, BadFunc> {
        if gs.is_empty() {
            panic!("can't apply, use const instead")
        }
        let Arity(_, g_in) = gs[0].arity();
        let mut g_stack = Func::empty(g_in);

        for g in gs.iter().rev() {
            g_stack = Func::stack(g.clone(), g_stack)?
        }

        Func::comp(f.clone(), g_stack)
    }

    pub fn eye(arity: u32) -> Func {
        let mut res = Func::empty(arity);
        for i in (0..arity).rev() {
            res = Func::stack(Func::proj(i, arity).unwrap(), res).unwrap()
        }
        res
    }

    pub fn z_eye(arity: u32) -> Func {
        Func::stack(
            Func::mk_const(arity - 1, Func::z()).unwrap(),
            Func::eye(arity - 1),
        )
        .unwrap()
    }

    pub fn s_eye(arity: u32) -> Func {
        let mut res = Func::empty(arity);
        for i in (0..arity).rev() {
            res = Func::stack(Func::proj(i, arity).unwrap(), res).unwrap()
        }
        res
    }

    pub fn set_tag(self, tag: Tag) -> Func {
        let Func(view, _) = self;
        Func(view, tag)
    }

    // Instance methods.
    pub fn view(&self) -> &View {
        &*self.0
    }

    pub fn into_view(self) -> View {
        (*self.0).clone()
    }

    pub fn tag(&self) -> &Tag {
        &self.1
    }

    pub fn arity(&self) -> Arity {
        match self.view() {
            View::Z => Arity(1, 0),
            View::S => Arity(1, 1),
            &View::Proj(_, arity) => Arity(1, arity),
            &View::Empty(arity) => Arity(0, arity),
            View::Stack(_, cdr) => {
                let Arity(cdr_out, cdr_in) = cdr.arity();
                Arity(cdr_out + 1, cdr_in)
            }
            View::Comp(f, g) => {
                let Arity(f_out, _) = f.arity();
                let Arity(_, g_in) = g.arity();
                Arity(f_out, g_in)
            }
            View::Rec(z_case, _) => {
                let Arity(_, z_in) = z_case.arity();
                Arity(1, z_in + 1)
            }
        }
    }

    pub fn unwrap_singleton(&self) -> Func {
        if let View::Stack(car, cdr) = self.view() {
            if let View::Empty(_) = cdr.view() {
                return car.unwrap_singleton();
            }
        }

        self.clone()
    }

    pub fn as_const(&self) -> Option<(Func, u32)> {
        if let View::Comp(f, g) = self.view() {
            if let &View::Empty(arity) = g.view() {
                return Some((f.clone(), arity));
            }
        }
        None
    }

    pub fn as_int(&self) -> Option<(u32, Option<u32>)> {
        if let Some((f, arity)) = self.as_const() {
            return f.as_int().map(|(value, _)| (value, Some(arity)));
        }
        if let View::Z = self.view() {
            return Some((0, None));
        }
        if let View::Comp(f, g) = self.view() {
            if let (View::S, View::Stack(car, cdr)) = (f.view(), g.view()) {
                return car.as_int().map(|(value, arity)| (value + 1, arity));
            }
        }
        None
    }

    pub fn as_application(&self) -> Option<(Vec<Func>, Vec<Func>)> {
        fn stack_to_backwards_vec(func: &Func) -> Vec<Func> {
            match func.view() {
                View::Empty(_) => vec![],
                View::Stack(car, cdr) => {
                    let mut cdr_vec = stack_to_backwards_vec(&*cdr);
                    cdr_vec.push(car.clone());
                    cdr_vec
                }
                _ => vec![func.clone()],
            }
        }

        if let View::Comp(f, g) = self.view() {
            return Some((
                stack_to_backwards_vec(f).into_iter().rev().collect(),
                stack_to_backwards_vec(g).into_iter().rev().collect(),
            ));
        }
        None
    }
    pub fn as_application2(&self) -> Option<(StackHelper, StackHelper)> {
        fn stack_to_backwards_vec(func: &Func) -> StackHelper {
            match func.view() {
                View::Empty(arity) => StackHelper {
                    args: vec![],
                    arity_in: *arity,
                },
                View::Stack(car, cdr) => {
                    let mut cdr_vec = stack_to_backwards_vec(&*cdr);
                    cdr_vec.args.push(car.clone());
                    cdr_vec
                }
                _ => StackHelper {
                    args: vec![func.clone()],
                    arity_in: func.arity().r#in(),
                },
            }
        }

        if let View::Comp(f, g) = self.view() {
            let f_res = stack_to_backwards_vec(f);
            let g_res = stack_to_backwards_vec(g);
            return Some((
                StackHelper {
                    args: f_res.args.into_iter().rev().collect(),
                    ..f_res
                },
                StackHelper {
                    args: g_res.args.into_iter().rev().collect(),
                    ..g_res
                },
            ));
        }
        None
    }
}
struct StackHelper {
    args: Vec<Func>,
    arity_in: u32,
}

impl SyntaxEq for Func {
    fn syntax_eq(&self, other: &Self) -> bool {
        match (self.view(), other.view()) {
            (View::Z, View::Z) => true,
            (View::Z, _) => false,
            (View::S, View::S) => true,
            (View::S, _) => false,
            (View::Proj(s_select, s_arity), View::Proj(o_select, o_arity)) => {
                s_select == o_select && s_arity == o_arity
            }
            (View::Proj(_, _), _) => false,
            (View::Empty(s_arity), View::Empty(o_arity)) => s_arity == o_arity,
            (View::Empty(_), _) => false,
            (View::Stack(s_car, s_cdr), View::Stack(o_car, o_cdr)) => {
                s_car.syntax_eq(o_car) && s_cdr.syntax_eq(o_cdr)
            }
            (View::Stack(_, _), _) => false,
            (View::Comp(s_f, s_g), View::Comp(o_f, o_g)) => {
                s_f.syntax_eq(o_f) && s_g.syntax_eq(o_g)
            }
            (View::Comp(_, _), _) => false,
            (View::Rec(s_f, s_g), View::Rec(o_f, o_g)) => s_f.syntax_eq(o_f) && s_g.syntax_eq(o_g),
            (View::Rec(_, _), _) => false,
        }
    }
}

impl fmt::Debug for Func {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn write(func: &Func, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
            let Func(_, tag) = func;
            if !fmt.alternate() {
                match tag {
                    Tag::None => (),
                    Tag::Alias(name) => return fmt.write_str(name),
                }
                //                let func = func.unwrap_singleton();

                // if let Some((f, arity)) = func.as_const() {
                //     fmt.write_fmt(format_args!("(const {} ", arity))?;
                //     write(&f, fmt)?;
                //     return fmt.write_str(")");
                // }

                if let Some((i, arity)) = func.as_int() {
                    if let Some(arity) = arity {
                        return fmt.write_fmt(format_args!("((int {}) * !{})", i, arity));
                    } else {
                        return fmt.write_fmt(format_args!("(int {})", i));
                    }
                }
                if let Some((fs, gs)) = func.as_application2() {
                    // Special case for normal function application.
                    if fs.args.len() == 1 && 0 < gs.args.len() {
                        fmt.write_str("(")?;
                        write(&fs.args[0], fmt)?;

                        for g in gs.args {
                            fmt.write_str(" ")?;
                            write(&g, fmt)?;
                        }
                        return fmt.write_str(")");
                    }

                    fn write_stack(sh: &StackHelper, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                        if sh.args.len() == 0 {
                            return fmt.write_fmt(format_args!("!{}", sh.arity_in));
                        }
                        if sh.args.len() == 1 {
                            return write(&sh.args[0], fmt);
                        }
                        fmt.write_str("<")?;
                        let mut iter = sh.args.iter();
                        write(&iter.next().unwrap(), fmt)?;
                        for a in iter {
                            fmt.write_str("; ")?;
                            write(&a, fmt)?;
                        }
                        return fmt.write_str(">");
                    }

                    fmt.write_str("(")?;
                    write_stack(&fs, fmt);
                    fmt.write_str(" * ")?;
                    write_stack(&gs, fmt);
                    return fmt.write_str(")");

                    // match (f_iter.next(), f_iter.peek(), g_iter.next()) {
                    //     (Some(f_init), None, Some(g_init)) => {

                    //     }
                    //     (o_f_init, _, o_g_init) => {

                    //     }

                    //     (None, None, None) => {
                    //         fmt.write_fmt(format_args!("(!{} * !{})", fs.arity_in, gs.arity_in))?
                    //     }
                    //     (None, None, Some(g_init)) => {
                    //         fmt.write_fmt(format_args!("(!{} * ", fs.arity_in))?;
                    //         write(&g_init, fmt)?;
                    //         for g in g_iter {
                    //             fmt.write_str(" ")?;
                    //             write(&g, fmt)?;
                    //         }
                    //         fmt.write_str(")")?;
                    //     }

                    //     (Some(f_init), None, None) => {
                    //         fmt.write_str("(")?;
                    //         write(&f_init, fmt)?;
                    //         fmt.write_fmt(format_args!(" * !{})", gs.arity_in))?
                    //     }
                    //     (Some(f_init), Some(_), None) => {
                    //         fmt.write_str("(<")?;
                    //         write(&f_init, fmt)?;
                    //         for f in f_iter {
                    //             fmt.write_str("; ")?;
                    //             write(&f_init, fmt)?;
                    //         }
                    //         fmt.write_fmt(format_args!("> * !{})", gs.arity_in))?
                    //     }
                    //     (Some(f_init), Some(_), Some(g_init)) => {
                    //         fmt.write_str("(<")?;
                    //         write(&f_init, fmt)?;
                    //         for f in f_iter {
                    //             fmt.write_str("; ")?;
                    //             write(&f, fmt)?;
                    //         }
                    //         fmt.write_str("> * ")?;
                    //         if let Some(_) = g_iter.peek() {
                    //             fmt.write_str("<")?;
                    //             write(&g_init, fmt)?;
                    //             for g in g_iter {
                    //                 fmt.write_str("; ")?;
                    //                 write(&g, fmt)?;
                    //             }
                    //             fmt.write_str(">")?;
                    //         } else {
                    //             write(&g_init, fmt)?;
                    //         }
                    //         fmt.write_str(")")?;
                    //     }
                    // }
                }
            }

            match func.view() {
                View::Z => fmt.write_str("Z"),
                View::S => fmt.write_str("S"),
                &View::Proj(select, arity) => {
                    fmt.write_fmt(format_args!("(proj {} {})", select, arity))
                }

                &View::Empty(arity) => fmt.write_fmt(format_args!("(empty {})", arity)),
                View::Stack(car, cdr) => {
                    fmt.write_str("(stack ")?;
                    write(car, fmt)?;
                    fmt.write_str(" ")?;
                    write(cdr, fmt)?;
                    fmt.write_str(")")
                }
                View::Comp(f, g) => {
                    fmt.write_str("(comp ")?;
                    write(f, fmt)?;
                    fmt.write_str(" ")?;
                    write(g, fmt)?;
                    fmt.write_str(")")
                }
                View::Rec(z_case, s_case) => {
                    fmt.write_str("(rec ")?;
                    write(z_case, fmt)?;
                    fmt.write_str(" ")?;
                    write(s_case, fmt)?;
                    fmt.write_str(")")
                }
            }
        }
        write(self, fmt)
    }
}

#[macro_export]
macro_rules! func {
    (Z) => {$crate::func::Func::z()};
    (S) => {$crate::func::Func::s()};
    ((int $value:tt)) => {$crate::func::Func::int($value)};
    ((rec $f:tt $g:tt)) => {
        $crate::func::Func::rec(func![$f], func![$g]).unwrap()
    };
    ((proj $select:tt $arity:tt)) => {
        $crate::func::Func::proj($select, $arity).unwrap()
    };
    ((const $arity:tt $f:tt)) => {
        $crate::func::Func::mk_const($arity, func![$f]).unwrap()
    };
    ((comp $f:tt $g:tt)) => {
        $crate::func::Func::comp(func![$f], func![$g]).unwrap()
    };
    (($f:tt $($gs:tt)+)) => {
        $crate::func::Func::apply(func![$f], &[$(func![$gs]),+]).unwrap()
    };
    ($f:ident) => {$f.clone()};
}

#[macro_export]
macro_rules! func_let {
    ($(let $name:ident = $fun:tt;)*) => {
        $(
            let $name = func![$fun].set_tag($crate::func::Tag::Alias(stringify!($name)));
        )*
    };
}
