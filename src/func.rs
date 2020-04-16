use std::fmt;
use std::rc::Rc;

#[derive(Debug, Clone)]
pub enum View {
    // Base functions.
    Z,
    S,

    // Projection functions.
    Select(u32),
    Skip(u32),

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
pub struct Arity(u32, u32);

#[derive(Debug, Clone)]
pub enum Tag {
    None,
    Alias(&'static str),
    Int(u32),
    Proj(u32, u32),
    Const(u32, Box<Func>),
    Applicaton(Box<Func>, Vec<Box<Func>>),
}

#[derive(Debug)]
pub enum BadFunc {
    InvalidSelect(u32),
    InvalidSkip(u32),
    InvalidProjection(u32, u32),
    StackCarOutArityMustBe1(Func),
    StackArityMismatch(Func, Func),
    CompArityMismatch(Func, Func),
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

    pub fn select(arity: u32) -> Result<Func, BadFunc> {
        if arity < 1 {
            Err(BadFunc::InvalidSelect(arity))
        } else {
            Ok(Func(Rc::new(View::Select(arity)), Tag::None))
        }
    }

    pub fn skip(arity: u32) -> Result<Func, BadFunc> {
        if arity < 1 {
            Err(BadFunc::InvalidSkip(arity))
        } else {
            Ok(Func(Rc::new(View::Skip(arity)), Tag::None))
        }
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
    pub fn proj(select: u32, arity: u32) -> Result<Func, BadFunc> {
        if arity <= select {
            return Err(BadFunc::InvalidProjection(select, arity));
        }
        let mut res = Func::select(arity - select).expect("already checked arity");
        for ii in 1..=select {
            res = Func::comp(
                res,
                Func::skip(arity - select + ii).expect("already checked arity"),
            )
            .expect("already checked arity")
            .set_tag(Tag::Proj(ii, arity - select + ii))
        }
        Ok(res)
    }

    pub fn int(value: u32) -> Func {
        let mut res = Func::z().set_tag(Tag::Int(0));
        for ii in 0..value {
            res = Func::comp(Func::s(), res)
                .unwrap()
                .set_tag(Tag::Int(ii + 1));
        }
        res
    }

    pub fn mk_const(arity: u32, f: Func) -> Result<Func, BadFunc> {
        Ok(Func::comp(f.clone(), Func::empty(arity))?.set_tag(Tag::Const(arity, Box::new(f))))
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

        let res = Func::comp(f.clone(), g_stack)?;

        let boxed_gs = gs.iter().map(|g| Box::new(g.clone())).collect();
        Ok(res.set_tag(Tag::Applicaton(Box::new(f), boxed_gs)))
    }

    pub fn set_tag(self, tag: Tag) -> Func {
        let Func(view, _) = self;
        Func(view, tag)
    }

    // Instance methods.

    pub fn view(&self) -> &View {
        &*self.0
    }

    pub fn arity(&self) -> Arity {
        match self.view() {
            View::Z => Arity(1, 0),
            View::S => Arity(1, 1),
            &View::Select(arity) => Arity(1, arity),
            &View::Skip(arity) => Arity(arity - 1, arity),
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

    pub fn syntax_eq(&self, other: &Self) -> bool {
        match (self.view(), other.view()) {
            (View::Z, View::Z) => true,
            (View::Z, _) => false,
            (View::S, View::S) => true,
            (View::S, _) => false,
            (View::Select(s_arity), View::Select(o_arity)) => s_arity == o_arity,
            (View::Select(_), _) => false,
            (View::Skip(s_arity), View::Skip(o_arity)) => s_arity == o_arity,
            (View::Skip(_), _) => false,
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
                    Tag::Int(i) => return fmt.write_fmt(format_args!("(int {})", i)),
                    Tag::Proj(select, arity) => {
                        return fmt.write_fmt(format_args!("(proj {} {})", select, arity))
                    }
                    Tag::Const(arity, f) => {
                        fmt.write_fmt(format_args!("(const {} ", arity))?;
                        write(&*f, fmt)?;
                        return fmt.write_str(")");
                    }
                    Tag::Applicaton(f, gs) => {
                        if gs.is_empty() {
                            panic!("misleading application")
                        }
                        fmt.write_str("(")?;
                        write(&*f, fmt)?;
                        for g in gs {
                            fmt.write_str(" ")?;
                            write(&*g, fmt)?;
                        }
                        return fmt.write_str(")");
                    }
                }
            }

            match func.view() {
                View::Z => fmt.write_str("Z"),
                View::S => fmt.write_str("S"),
                &View::Select(arity) => fmt.write_fmt(format_args!("(select {})", arity)),
                &View::Skip(arity) => fmt.write_fmt(format_args!("(skip {})", arity)),

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
    (S) => {$crate::func::Func::z()};
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

// (comp (comp (comp (select 1) (skip 2)) (skip 3)) (stack Z (stack (comp S Z) (stack (comp S (comp S Z)) (empty 0)))))
// (comp (comp (select 1) (skip 2)) (comp (skip 3) (stack Z (stack (comp S Z) (stack (comp S (comp S Z)) (empty 0))))))
// (comp (comp (select 1) (skip 2)) (stack (comp S Z) (stack (comp S (comp S Z)) (empty 0)))))
