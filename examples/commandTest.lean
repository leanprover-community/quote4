import Qq.Commands
import Qq.Delab

open Qq Lean Elab Tactic

macro "trace_state" : doElem => `(doElem| (by trace_state; exact pure ()))
macro "trace_return" t:term : doElem => `(doElem| (by trace_state; exact pure $t))

-- using the goal type (interpret 2, 3 as Int)
/--
trace: x : Q(Prop)
inst✝ : Q(Decidable «$x»)
⊢ TermElabM Q(Int)
-/
#guard_msgs in
def f₁ (x : Prop) [Decidable x] : Int :=
  by_elabq
    trace_return q(if $x then 2 else 3)

def add_self_37 {α : Type u} [Add α] (a : α) : α :=
  by_elabq return (List.range 36).foldr (init := q($a)) fun _ acc => q($acc + $a)

/-- info: f₁ (x : Prop) [Decidable x] : Int -/
#guard_msgs in
#check f₁

-- without goal type
/--
trace: _x : Q(Int)
⊢ TermElabM Expr
-/
#guard_msgs in
def f₂ (_x : Int) := by_elabq
  trace_return q(5)

/-- info: f₂ (_x : Int) : Nat -/
#guard_msgs in
#check f₂

-- tactic without capturing the goal
/--
trace: a b : Q(Nat)
_h : Q(«$a» = «$b»)
p : Q(Prop) := q(«$a» = «$b»)
⊢ TacticM PUnit
-/
#guard_msgs in
example (a b : Nat) (_h : a = b) : True := by
  run_tacq
    let p : Q(Prop) := q($a = $b)
    trace_state
    let t ← Meta.inferType _h
  trivial

def assignQ {α : Q(Sort u)} (mvar : Q($α)) (val : Q($α)) : Meta.MetaM Unit :=
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
    logInfo m!"{goal.isMVar}"
    logInfo goal.ty
    assignQ q($goal) q(False.elim $h)

-- universes & let expressions

universe u v in
/--
trace: u v : Level
α : Q(Type u)
β : Q(Type v)
f₀ : Q(«$α» → «$β»)
f₁ : Q(«$β» → «$α»)
b : Q(«$β»)
h : Q(«$f₀» («$f₁» «$b») = «$b»)
f₂ : Q(«$β» → «$β»)
f₂_eq✝ : «$f₂» =Q «$f₀» ∘ «$f₁»
goal : Q(«$b» = «$f₂» «$b»)
⊢ TacticM PUnit
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

universe u v in
/--
trace: u v : Level
α : Q(Type u)
β : Q(Type v)
f₀ : Q(«$α» → «$β»)
f₁ : Q(«$β» → «$α»)
b : Q(«$β»)
h : Q(«$f₀» («$f₁» «$b») = «$b»)
f₂ : Q(«$β» → «$β»)
f₂_eq✝ : «$f₂» =Q «$f₀» ∘ «$f₁»
⊢ TermElabM Q(«$b» = «$f₀» («$f₁» «$b»))
-/
#guard_msgs in
example {α : Type u} {β : Type v} (f₀ : α → β) (f₁ : β → α)
    (b : β) (h : f₀ (f₁ b) = b) :
    b = f₀ (f₁ b) :=
  let f₂ := f₀ ∘ f₁
  by_elabq
    trace_return q(Eq.symm $h)
