import Qq
open Qq Lean

partial def summands : Q(Nat) → MetaM (List Q(Nat))
  | ~q($x + $y) => return (← summands x) ++ (← summands y)
  | n => return [n]

opaque k : Nat
opaque m : Nat

abbrev double (a : Nat) := a + a

#eval summands q(double k + m)

abbrev square (a : Nat) :=
  have : Add Nat := ⟨(· * ·)⟩
  a + a

#eval square 10
#eval summands q(square k + m)