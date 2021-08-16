import Qq
open Qq Lean

def provePositive (n : Q(Nat)) : MetaM Q(0 < $n) :=
  match n with
    | ~q($m + 1) => pure q(Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_succ_self _))
    | ~q(1 + $m) => pure q(by
        rw [Nat.add_comm]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_succ_self _))
    | _ => throwError "cannot prove positive: {n}"

#eval provePositive q(42)
