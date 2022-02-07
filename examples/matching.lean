import Qq
open Qq Lean

partial def summands : Q(Nat) → MetaM (List Q(Nat))
  | ~q($x + $y) => return (← summands x) ++ (← summands y)
  | n => return [n]

abbrev double (a : Nat) := a + a

#eval summands q(double 42 + 7)
