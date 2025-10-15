import Qq
open Qq

set_option linter.unusedVariables false in
def typeClassArgument (α : Q(Sort u)) (inst : Q(Inhabited $α)) : Q($α) :=
  q(Inhabited.default)

example : Q(Nat) :=
  typeClassArgument q(Nat) q(inferInstance)

/--
info: ((Expr.const `Inhabited.default [Level.zero.succ]).app (Expr.const `Nat [])).app
  (((Expr.const `inferInstance [Level.zero.succ]).app
        ((Expr.const `Inhabited [Level.zero.succ]).app (Expr.const `Nat []))).app
    (Expr.const `instInhabitedNat []))
-/
#guard_msgs in
open Lean in
#eval show MetaM Q(Nat) from do
  let _ ← synthInstanceQ q(Inhabited Nat)
  return typeClassArgument (u := levelOne) q(Nat) q(inferInstance)
