import Qq
open Qq Lean

def provePositive (n : Q(Nat)) : MetaM Q(0 < $n) :=
  match n with
    | ~q($m + 1) => pure q(Nat.ltOfLeOfLt (Nat.zeroLe _) (Nat.ltSuccSelf _))
    | ~q(1 + $m) => pure q(by
        rw [Nat.add_comm]
        exact Nat.ltOfLeOfLt (Nat.zeroLe _) (Nat.ltSuccSelf _))
    | _ => throwError "cannot prove positive: {n}"

#eval provePositive q(42)
