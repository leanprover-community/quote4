import Qq
open Qq

def typeClassArgument (α : Q(Sort u)) [Q(Inhabited α)] : Q(α) :=
  q(Inhabited.default)

example : Q(Nat) :=
  let x : Q(Inhabited Nat) := q(inferInstance)
  typeClassArgument q(Nat)

open Lean in
#eval show MetaM Q(Nat) from do
  let _ ← synthInstanceQ q(Inhabited Nat)
  let x : Q(Nat) := q(Inhabited.default)
  typeClassArgument q(Nat)