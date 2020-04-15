
// Path 1.
//
// - Id(f): f
//   - Fwd needs: N/A
//   - Rev needs: ()
// - CompAssoc(f, g, h): ((f g) h) -> (f (g h))
//   - Fwd needs: ()
//   - Rev needs: ()
// - SkipStack(arity, car, cdr): ((skip arity) (stack car cdr)) -> cdr
//   - Fwd needs: ()
//   - Rev needs: (arity, car)
// - RecZ(z_case, s_case): ((rec z_case s_case) Z) -> z_case
//   - Fwd needs: ()
//   - Rev needs: (s_case)

// Path 2.
//
// - Refl(f): (f ~ f)
//   - Fwd needs: N/A
//   - Rev needs: ()
// - Symm(f, g): (f ~ g) -> (g ~ f)
//   - Fwd needs: ()
//   - Rev needs: ()
// - Lift(f, g, h, path1 : (f -> g)): (f ~ h) -> (g ~ h)
//   - Fwd needs: (path1)
//   - Rev needs: (path1)
// - CompLeft: (f, f', g) -> (f ~ f') -> ((f g) ~ (f' g))
//   - Rev: ((f g) ~ (f' g)) -> () -> (f ~ f')
// 
// Goal is 


// ProtoTrans(g).needs
// 

// 3-Path
//
// Refl: (f, g, p : (f ~ g)) -> (p ~ p)
// Trans: (f, g, h, i, j, p: (i ~ j)) -> ((f ~ g) -> (h ~ i)) -> ((f ~ g) -> (h ~ j))
// - Rev: ((f ~ g) -> (h ~ j)) -> (i ~ j) -> ((f ~ g) -> (h ~ j))
//
// Goal becomes: refl -> 