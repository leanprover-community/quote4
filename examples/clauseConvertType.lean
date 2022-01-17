import Qq
open Qq Lean

/-!
Type-safe conversion from values of type `Sum α β` to values of type `Sum α (Sum β Empty)`.
-/

def orLevel : (ps : List ((u : Level) × Q(Type u))) → Level
  | [] => levelZero
  | ⟨u, p⟩ :: ps => mkLevelMax u (orLevel ps)

def or1 : (ps : List ((u : Level) × Q(Type u))) → Q(Type $(orLevel ps))
  | [] => q(Empty)
  | [⟨u, p⟩] => q($p)
  | ⟨u, p⟩::ps => q(Sum $p $(or1 ps))

def or2 : (ps : List ((u : Level) × Q(Type u))) → Q(Type $(orLevel ps))
  | [] => q(Empty)
  | ⟨u, p⟩ :: ps => q(Sum $p $(or2 ps))

def orChange : (ps : List ((u : Level) × Q(Type u))) → Q($(or1 ps) → $(or2 ps))
  | [] => q(id)
  | [⟨u, p⟩] => q(Sum.inl)
  | ⟨u, p⟩::(ps1::ps2) =>
    let h := orChange (ps1::ps2)
    q(fun h => match h with
      | Sum.inl l => Sum.inl l
      | Sum.inr r => Sum.inr ($h r))
