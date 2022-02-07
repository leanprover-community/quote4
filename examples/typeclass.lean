import Qq
open Qq

def typeClassArgument (α : Q(Sort u)) (inst : Q(Inhabited $α)) : Q($α) :=
  q(Inhabited.default)

example : Q(Nat) :=
  typeClassArgument q(Nat) q(inferInstance)

open Lean in
#eval show MetaM Q(Nat) from do
  let _ ← synthInstanceQ q(Inhabited Nat)
  return typeClassArgument q(Nat) q(inferInstance)
