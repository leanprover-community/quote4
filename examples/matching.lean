import Qq
open Qq Lean

partial def summands : Q(Nat) → MetaM (List Q(Nat))
  | ~q(x + y) => do pure $ (← summands x) ++ (← summands y)
  | n => [n]

abbrev double (a : Nat) := a + a

#eval summands q(double 42 + 7)
