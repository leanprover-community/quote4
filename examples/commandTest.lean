import Qq

open Qq

macro "trace_state" : doElem => `(doElem| pure (by trace_state; exact ()))

-- using the goal type (interpret 2, 3 as Int)
/--
trace: x : Q(Prop)
inst✝ : Q(Decidable «$x»)
⊢ PUnit
-/
#guard_msgs in
def f (x : Prop) [Decidable x] : Int :=
  by_elabq
    trace_state
    return q(if $x then 2 else 3)

-- without goal type
def x := q(5)

-- tactic without capturing the goal
/--
trace: a b : Q(Nat)
_h : Q(«$a» = «$b»)
⊢ PUnit
-/
#guard_msgs in
example (a b : Nat) (_h : a = b) : True := by
  run_tacq
    trace_state
    let p : Q(Prop) := q($a = $b)
    let t ← Lean.Meta.inferType _h
  trivial

def assignQ {α : Q(Sort u)} (mvar : Q($α)) (val : Q($α)) : Lean.Meta.MetaM Unit :=
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
    assignQ q($goal) q(False.elim $h)

-- universes & let expressions

universe u v
/--
trace: v u : Lean.Level
α : Q(Type u)
β : Q(Type v)
f₀ : Q(«$α» → «$β»)
f₁ : Q(«$β» → «$α»)
b : Q(«$β»)
h : Q(«$f₀» («$f₁» «$b») = «$b»)
f₂ : Q(«$β» → «$β»)
f₂.eq✝ : «$f₂» =Q «$f₀» ∘ «$f₁»
goal : Q(«$b» = «$f₂» «$b»)
⊢ PUnit
-/
#guard_msgs in
example {α : Type u} {β : Type v} (f₀ : α → β) (f₁ : β → α)
    (b : β) (h : f₀ (f₁ b) = b) :
    let f₂ := f₀ ∘ f₁
    b = f₂ b := by
  intro f₂
  run_tacq goal =>
    trace_state
    assignQ q($goal) q(Eq.symm $h)
