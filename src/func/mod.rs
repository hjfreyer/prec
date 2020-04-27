pub mod actions;
pub mod tactics;

use crate::base;
use crate::base::SyntaxEq;
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

#[derive(Debug, Clone, Copy)]
pub struct Arity {
    pub out: u32,
    pub r#in: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
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
        let car_arity = car.arity();

        if car_arity.out != 1 {
            return Err(BadFunc::StackCarOutArityMustBe1(car));
        }
        if car_arity.r#in != cdr.arity().r#in {
            return Err(BadFunc::StackArityMismatch(car, cdr));
        }

        Ok(Func(Rc::new(View::Stack(car, cdr)), Tag::None))
    }

    pub fn comp(f: Func, g: Func) -> Result<Func, BadFunc> {
        match g.view() {
            View::Empty(_) | View::Stack(_, _) | View::Comp(_, _) => (),
            _ => return Err(BadFunc::CompRightMustBeCompOrStack(f, g)),
        }

        if f.arity().r#in != g.arity().out {
            Err(BadFunc::CompArityMismatch(f, g))
        } else {
            Ok(Func(Rc::new(View::Comp(f, g)), Tag::None))
        }
    }

    pub fn rec(z_case: Func, s_case: Func) -> Result<Func, BadFunc> {
        let z_arity = z_case.arity();
        let s_arity = s_case.arity();
        if z_arity.out != 1 {
            return Err(BadFunc::RecZCaseOutArityMustBe1(z_case));
        }
        if s_arity.out != 1 {
            return Err(BadFunc::RecSCaseOutArityMustBe1(s_case));
        }
        if z_arity.r#in + 2 != s_arity.r#in {
            return Err(BadFunc::RecArityMismatch(z_case, s_case));
        }

        Ok(Func(Rc::new(View::Rec(z_case, s_case)), Tag::None))
    }

    // Helper constructors.
    pub fn int(value: u32) -> Func {
        let mut res = Func::z();
        for _ in 0..value {
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
        let mut g_stack = Func::empty(gs[0].arity().r#in);

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
        for i in (1..arity).rev() {
            res = Func::stack(Func::proj(i, arity).unwrap(), res).unwrap()
        }
        Func::stack(
            Func::apply(Func::s(), &[Func::proj(0, arity).unwrap()]).unwrap(),
            res,
        )
        .unwrap()
    }

    pub fn set_tag(self, tag: Tag) -> Func {
        let Func(view, _) = self;
        Func(view, tag)
    }

    // Eliminators.
    pub fn unz(&self) -> Option<()> {
        if let View::Z = self.view() {
            Some(())
        } else {
            None
        }
    }

    pub fn uns(&self) -> Option<()> {
        if let View::S = self.view() {
            Some(())
        } else {
            None
        }
    }

    pub fn unproj(&self) -> Option<(u32, u32)> {
        if let View::Proj(select, arity) = self.view() {
            Some((select, arity))
        } else {
            None
        }
    }

    pub fn unempty(&self) -> Option<u32> {
        if let View::Empty(arity) = self.view() {
            Some(arity)
        } else {
            None
        }
    }

    pub fn decompose(&self) -> Option<(Func, Func)> {
        if let View::Comp(f, g) = self.view() {
            Some((f.clone(), g.clone()))
        } else {
            None
        }
    }

    pub fn unstack(&self) -> Option<(Func, Func)> {
        if let View::Stack(car, cdr) = self.view() {
            Some((car.clone(), cdr.clone()))
        } else {
            None
        }
    }

    pub fn unrec(&self) -> Option<(Func, Func)> {
        if let View::Rec(z_case, s_case) = self.view() {
            Some((z_case.clone(), s_case.clone()))
        } else {
            None
        }
    }

    // Instance methods.
    pub fn view(&self) -> View {
        (*self.0).clone()
    }

    pub fn into_view(self) -> View {
        (*self.0).clone()
    }

    pub fn tag(&self) -> Tag {
        self.1
    }

    pub fn arity(&self) -> Arity {
        match self.view() {
            View::Z => Arity { out: 1, r#in: 0 },
            View::S => Arity { out: 1, r#in: 1 },
            View::Proj(_, arity) => Arity {
                out: 1,
                r#in: arity,
            },
            View::Empty(arity) => Arity {
                out: 0,
                r#in: arity,
            },
            View::Stack(_, cdr) => {
                let cdra = cdr.arity();
                Arity {
                    out: cdra.out + 1,
                    r#in: cdra.r#in,
                }
            }
            View::Comp(f, g) => Arity {
                out: f.arity().out,
                r#in: g.arity().r#in,
            },
            View::Rec(z_case, _) => Arity {
                out: 1,
                r#in: z_case.arity().r#in + 1,
            },
        }
    }

    fn as_const(&self) -> Option<(Func, u32)> {
        if let View::Comp(f, g) = self.view() {
            if let View::Empty(arity) = g.view() {
                return Some((f.clone(), arity));
            }
        }
        None
    }

    fn as_int(&self) -> Option<(u32, Option<u32>)> {
        if let Some((f, arity)) = self.as_const() {
            return f.as_int().map(|(value, _)| (value, Some(arity)));
        }
        if let View::Z = self.view() {
            return Some((0, None));
        }
        if let View::Comp(f, g) = self.view() {
            if let (View::S, View::Stack(car, _)) = (f.view(), g.view()) {
                return car.as_int().map(|(value, arity)| (value + 1, arity));
            }
        }
        None
    }

    fn as_application(&self) -> Option<(StackHelper, StackHelper)> {
        fn stack_to_backwards_vec(func: &Func) -> StackHelper {
            match func.view() {
                View::Empty(arity) => StackHelper {
                    tag: Tag::None,
                    args: vec![],
                    arity_in: arity,
                },
                View::Stack(car, cdr) => {
                    let mut cdr_vec = stack_to_backwards_vec(&cdr);
                    cdr_vec.args.push(car.clone());
                    cdr_vec
                }
                _ => StackHelper {
                    tag: Tag::None,
                    args: vec![func.clone()],
                    arity_in: func.arity().r#in,
                },
            }
        }

        if let View::Comp(f, g) = self.view() {
            let f_res = stack_to_backwards_vec(&f);
            let g_res = stack_to_backwards_vec(&g);
            return Some((
                StackHelper {
                    tag: f.tag(),
                    args: f_res.args.into_iter().rev().collect(),
                    ..f_res
                },
                StackHelper {
                    tag: g.tag(),
                    args: g_res.args.into_iter().rev().collect(),
                    ..g_res
                },
            ));
        }
        None
    }
}
struct StackHelper {
    tag: Tag,
    args: Vec<Func>,
    arity_in: u32,
}

impl base::Point for Func {}

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
                s_car.syntax_eq(&o_car) && s_cdr.syntax_eq(&o_cdr)
            }
            (View::Stack(_, _), _) => false,
            (View::Comp(s_f, s_g), View::Comp(o_f, o_g)) => {
                s_f.syntax_eq(&o_f) && s_g.syntax_eq(&o_g)
            }
            (View::Comp(_, _), _) => false,
            (View::Rec(s_f, s_g), View::Rec(o_f, o_g)) => {
                s_f.syntax_eq(&o_f) && s_g.syntax_eq(&o_g)
            }
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

                if let Some((i, arity)) = func.as_int() {
                    if let Some(arity) = arity {
                        return fmt.write_fmt(format_args!("((int {}) * !{})", i, arity));
                    } else {
                        return fmt.write_fmt(format_args!("(int {})", i));
                    }
                }
                if let Some((fs, gs)) = func.as_application() {
                    // Special case for normal function application.
                    if fs.args.len() == 1 && 0 < gs.args.len() && gs.tag == Tag::None {
                        fmt.write_str("(")?;
                        write(&fs.args[0], fmt)?;

                        for g in gs.args {
                            fmt.write_str(" ")?;
                            write(&g, fmt)?;
                        }
                        return fmt.write_str(")");
                    }

                    if fs.args.len() == 0 {
                        return fmt.write_fmt(format_args!("(!{} * ...)", fs.arity_in));
                    }

                    fn write_stack(sh: &StackHelper, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
                        if let Tag::Alias(name) = sh.tag {
                            return fmt.write_fmt(format_args!("{}", name));
                        }

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
                    write_stack(&fs, fmt)?;
                    fmt.write_str(" * ")?;
                    write_stack(&gs, fmt)?;
                    return fmt.write_str(")");
                }
            }

            match func.view() {
                View::Z => fmt.write_str("Z"),
                View::S => fmt.write_str("S"),
                View::Proj(select, arity) => {
                    fmt.write_fmt(format_args!("(proj {} {})", select, arity))
                }

                View::Empty(arity) => fmt.write_fmt(format_args!("(empty {})", arity)),
                View::Stack(car, cdr) => {
                    fmt.write_str("(stack ")?;
                    write(&car, fmt)?;
                    fmt.write_str(" ")?;
                    write(&cdr, fmt)?;
                    fmt.write_str(")")
                }
                View::Comp(f, g) => {
                    fmt.write_str("(comp ")?;
                    write(&f, fmt)?;
                    fmt.write_str(" ")?;
                    write(&g, fmt)?;
                    fmt.write_str(")")
                }
                View::Rec(z_case, s_case) => {
                    fmt.write_str("(rec ")?;
                    write(&z_case, fmt)?;
                    fmt.write_str(" ")?;
                    write(&s_case, fmt)?;
                    fmt.write_str(")")
                }
            }
        }
        write(self, fmt)
    }
}

#[macro_export]
macro_rules! func {
    (@stack $car:tt $($cdr:tt)+) => {
        $crate::func::Func::stack(func![$car], func![@stack $($cdr)+]).unwrap()
    };
    (@stack $f:tt) => {
        {
            let f = func![$f];
            let f_arity = f.arity();
            $crate::func::Func::stack(f, $crate::func::Func::empty(f_arity.r#in)).unwrap()
        }
    };
    (@compose_chain $f:tt) => {
        func![$f]
    };
    (@compose_chain $f:tt $($gs:tt)+) => {
        $crate::func::Func::comp(func![$f], func![@compose_chain $($gs)+]).unwrap()
    };
    (Z) => {$crate::func::Func::z()};
    (S) => {$crate::func::Func::s()};
    ((int $value:tt)) => {$crate::func::Func::int($value)};
    ((rec $f:tt $g:tt)) => {
        $crate::func::Func::rec(func![$f], func![$g]).unwrap()
    };
    ((proj $select:tt $arity:tt)) => {
        $crate::func::Func::proj($select, $arity).unwrap()
    };
    ((! $arity:expr)) => {
        $crate::func::Func::empty($arity)
    };
    ((s_i $arity:expr)) => {
        $crate::func::Func::s_eye($arity)
    };
    ((z_i $arity:expr)) => {
        $crate::func::Func::z_eye($arity)
    };
    ([$($fs:tt),+]) => {
        func![@stack $($fs)*]
    };
    (($f:tt $(*$gs:tt)+)) => {
        func![@compose_chain $f $($gs)+]
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
