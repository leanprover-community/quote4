import Lean
import Qq.Macro

open Qq
open Lean Meta Elab Tactic Command

elab "iff_constructor" : tactic => do
  let mvarId ← getMainGoal
  let goalType ← getMainTarget

  let_expr Iff a b := goalType
    | throwError "Goal type is not of the form `a ↔ b`"

  let a : Q(Prop) := a
  let b : Q(Prop) := b

  let mvarId1 ← mkFreshExprMVar q($a → $b) (userName := `mp)
  let mvarId2 ← mkFreshExprMVar q($b → $a) (userName := `mpr)

  let mvarId1 : Q($a → $b) := mvarId1
  let mvarId2 : Q($b → $a) := mvarId2

  mvarId.assign q(@Iff.intro $a $b $mvarId1 $mvarId2)

  modify fun _ => { goals := [mvarId1.mvarId!, mvarId2.mvarId!] }

example (p q : Prop) (h1 : p → q) (h2 : q → p) : p ↔ q := by
  iff_constructor

  case mp => assumption
  case mpr => assumption
