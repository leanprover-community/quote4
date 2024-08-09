import Qq
open Qq Lean

-- TODO: this linter crashes on the `def` below
set_option linter.constructorNameAsVariable false in
def turnExistsIntoForall : Q(Prop) → MetaM Q(Prop)
  | ~q(∃ x y, $p x y) => return q(∀ x y, $p x y)
  | e => return e

/-- info: ∀ (x : String) (y : Nat), x.length ≤ y + 42 -/
#guard_msgs in
run_cmd Elab.Command.liftTermElabM do
  Lean.logInfo <| ← turnExistsIntoForall q(∃ a b, String.length a ≤ b + 42)
