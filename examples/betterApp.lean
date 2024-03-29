import Qq
open Qq

set_option trace.compiler.ir.result true in

-- Note: `betterApp` actually has two additional parameters
-- `{u v : Lean.Level}` auto-generated due to option
-- `autoBoundImplicitLocal`.

def betterApp {α : Q(Sort $u)} {β : Q($α → Sort $v)}
    (f : Q((a : $α) → $β a)) (a : Q($α)) : Q($β $a) :=
  q($f $a)

#eval betterApp q(Int.toNat) q(42)

#check betterApp (β := q(fun n : Nat => Fin (n+1))) q(fun a => ⟨a, Nat.lt_succ_self _⟩) q(42)
