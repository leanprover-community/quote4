import Qq
open Qq Lean

partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) :
    Q($α) → MetaM (List Q($α))
  | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
  | n => return [n]

opaque k : Nat
opaque m : Nat

abbrev double (a : Nat) := a + a

#eval summands q(inferInstance) q(double k + m)

#eval show MetaM Bool from do
  let x : Q(Nat) := q(k + m)
  match x with
  | ~q(Nat.add $a $b) => return true
  | _ => return false

abbrev square (a : Nat) :=
  have : Add Nat := ⟨(· * ·)⟩
  a + a

#eval square 10
#eval summands q(inferInstance) q(k + square (square k))
#eval summands q(⟨(· * ·)⟩) q(k * square (square k))
