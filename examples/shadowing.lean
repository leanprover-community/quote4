import Qq
open Qq

-- TODO; use Std's `guard_msgs` instead
open Lean.Elab in
/-- `success_if_error% f with "msg"` expects `f` to emit the provided error -/
elab "success_if_error% " f:term " with " msg:str : term <= expected_type => do
  let initMsgs ← modifyGetThe Lean.Core.State fun st => (st.messages, { st with messages := {} })
  let fe ← Term.elabTerm f expected_type
  let msgs := (← getThe Lean.Core.State).messages.msgs.filter (·.severity == .error)
  modifyThe Lean.Core.State fun st => { st with messages := initMsgs }
  match msgs.toList with
  | m :: _ =>
    let ex_msg ← m.data.toString
    if ex_msg ≠ msg.getString then
      Lean.logErrorAt msg m!"got\n{ex_msg}\nexpected\n{msg}"
  | [] =>
    Lean.logErrorAt f "Elaborated with no error"
  return fe

/-
  This fails, the second definition of `n`, which is not of type `Nat`, shadows the first,
  `Nat`-typed, definition of `n`.
  Even if the second definition is not available inside the quotation (`Nat → Nat` does not implement `ToExpr`)
  we don't want `$n` to refer to the shadowed definition, that would be confusing
-/
example : Q(Nat) :=
  let n : Nat := 1
  let n : Nat := 2
  let n : Nat → Nat := fun _ => n
  success_if_error% q($n) with "unknown identifier '«$n»'"
