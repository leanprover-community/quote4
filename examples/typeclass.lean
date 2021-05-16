import Qq
open Qq

def typeClassArgument (α : Q(Sort u)) [Q(Inhabited α)] : Q(α) :=
  q(Inhabited.default)

example : Q(Nat) :=
  let x : Q(Inhabited Nat) := q(inferInstance)
  typeClassArgument q(Nat)