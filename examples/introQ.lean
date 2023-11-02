import Qq
open Qq Lean

def introQ {α : Q(Sort u)} {β : Q($α → Sort v)} (mvar : Q(∀ a, $β a)) (n : Name) :
    MetaM ((a : Q($α)) × Q($β $a)) := do
  let (f, v) ← mvar.mvarId!.intro n
  pure ⟨.fvar f, .mvar v⟩

def assignQ {α : Q(Sort u)} (mvar : Q($α)) (val : Q($α)) : MetaM Unit :=
  mvar.mvarId!.assign val

elab "demo" : term => do
  let P ← mkFreshExprMVarQ q(∀ {n : Nat}, n = 1)
  let ⟨_, m⟩ ← introQ q(@$P) `n
  m.mvarId!.withContext do
  assignQ q($m) q(sorry)
  instantiateMVars P

#check demo
