import Qq
open Qq

def typeClassArgument (α : Q(Sort u)) [Q(Inhabited α)] : Q(α) :=
  q(Inhabited.default)

open Lean in
example : Q(Nat) :=
  let x : Q(Inhabited Nat) := q(inferInstance)
  typeClassArgument (u := mkLevelSucc levelZero) q(Nat)