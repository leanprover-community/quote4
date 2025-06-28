import Qq

open Qq

-- using the goal type (interpret 2, 3 as Int)
/--
info: x
---
info: Prop
-/
#guard_msgs in
def f (x : Prop) [Decidable x] : Int :=
  by_elabq
    Lean.logInfo x
    Lean.logInfo x.ty
    return q(if $x then 2 else 3)

 #print f

-- without goal type
def x := q(5)

-- tactic without capturing the goal
/--
info: a = b
---
info: true
---
info: true
-/
#guard_msgs in
example (a b : Nat) (_h : a = b) : True := by
  run_tacq
    let p : Q(Prop) := q($a = $b)
    let t ← Lean.Meta.inferType _h
    Lean.logInfo p
    Lean.logInfo <| toString (← Lean.Meta.isDefEq t p)
    Lean.logInfo <| toString (← Lean.Meta.isDefEq _h.ty p)
  trivial

def assignQ {α : Q(Type)} (mvar : Q($α)) (val : Q($α)) : Lean.Meta.MetaM Unit :=
  mvar.mvarId!.assign val

-- tactic with capturing the goal
/--
info: true
---
info: a = b
-/
#guard_msgs in
example (a b : Nat) (h : False) : a = b := by
  run_tacq goal =>
    Lean.logInfo m!"{goal.isMVar}"
    Lean.logInfo goal.ty
    assignQ goal q(False.elim $h)

-- universes & let expressions

universe u v
/--
info: u
---
info: α
---
info: β → β
-/
#guard_msgs in
example {α : Type u} {β : Type v} (f₀ : α → β) (f₁ : β → α)
    (b : β) (h : f₀ (f₁ b) = b) :
    let f₂ := f₀ ∘ f₁
    b = f₂ b := by
  intro f₂
  run_tacq goal =>
    Lean.logInfo u
    Lean.logInfo α
    Lean.logInfo f₂.ty
    assignQ goal q(Eq.symm $h)
