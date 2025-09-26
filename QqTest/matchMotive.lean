import Qq
open Qq Lean

open Elab Term in
elab tk:"showTerm" t:term : term <= expectedType => do
  let t' ← withSynthesize do elabTerm t expectedType
  logAt tk t' (severity := MessageSeverity.information)
  return t'

/--
info: failed to pretty print expression (use 'set_option pp.rawOnError true' for raw representation)
-/
#guard_msgs in
def provePositive (n : Q(Nat)) : MetaM Q(0 < $n) :=
  showTerm match n with
    | ~q($m + 1) => pure q(Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_succ_self _))
    | ~q(1 + $m) => pure q(by
        show 0 < 1 + $m
        rw [Nat.add_comm]
        exact Nat.lt_of_le_of_lt (Nat.zero_le _) (Nat.lt_succ_self _))
    | _ => throwError "cannot prove positive: {n}"

/--
info: (((((Expr.const `Nat.lt_of_le_of_lt []).app
                  ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                        (Expr.lit (Literal.natVal 0))).app
                    ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 0))))).app
              ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                    (Expr.lit (Literal.natVal 41))).app
                ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 41))))).app
          ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 42))).app
            ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 42))))).app
      ((Expr.const `Nat.zero_le []).app
        ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 41))).app
          ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 41)))))).app
  ((Expr.const `Nat.lt_succ_self []).app
    ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 41))).app
      ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 41)))))
-/
#guard_msgs in
#eval provePositive q(42) >>= fun proof => pure proof <* proof.check
