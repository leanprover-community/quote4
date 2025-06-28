import Qq

open Qq

-- using the goal type (interpret 2, 3 as Int)
def f (x : Prop) [Decidable x] : Int :=
  by_elabq
    Lean.logInfo x
    Lean.logInfo x.ty
    return q(if $x then 2 else 3)

#print f

-- without goal type
def x := q(5)

-- tactic without capturing the goal
example (a b : Nat) (h : a = b) : True := by
  run_tacq
    let p : Q(Prop) := q($a = $b)
    let t ← Lean.Meta.inferType h
    Lean.logInfo p
    Lean.logInfo <| toString (← Lean.Meta.isDefEq t p)
    Lean.logInfo <| toString (← Lean.Meta.isDefEq h.ty p)
  trivial

def assignQ {α : Q(Type)} (mvar : Q($α)) (val : Q($α)) : Lean.Meta.MetaM Unit :=
  mvar.mvarId!.assign val

-- tactic with capturing the goal
example (a b : Nat) (h : False) : a = b := by
  run_tacq goal =>
    Lean.logInfo goal
    Lean.logInfo goal.ty
    assignQ goal q(False.elim $h)
