import Qq
open Qq

-- set_option trace.compiler.ir.result true in

-- Note: `betterApp` actually has two additional parameters
-- `{u v : Lean.Level}` auto-generated due to option
-- `autoBoundImplicitLocal`.

def betterApp {α : Q(Sort $u)} {β : Q($α → Sort $v)}
    (f : Q((a : $α) → $β a)) (a : Q($α)) : Q($β $a) :=
  q($f $a)

/--
info: (Lean.Expr.const `Int.toNat []).app
  ((((Lean.Expr.const `OfNat.ofNat [Lean.Level.zero]).app (Lean.Expr.const `Int [])).app
        (Lean.Expr.lit (Lean.Literal.natVal 42))).app
    ((Lean.Expr.const `instOfNat []).app (Lean.Expr.lit (Lean.Literal.natVal 42))))
-/
#guard_msgs in
#eval betterApp q(Int.toNat) q(42)
/--
info: betterApp q(fun a => ⟨a, ⋯⟩) q(42) : Q(Fin (42 + 1))
-/
#guard_msgs in
#check betterApp (β := q(fun n : Nat => Fin (n+1))) q(fun a => ⟨a, Nat.lt_succ_self _⟩) q(42)
