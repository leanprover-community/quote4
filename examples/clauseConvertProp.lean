import Qq
open Qq

/-!
Type-safe conversion from proofs of `a ∨ b` to proofs of `a ∨ b ∨ false`.
-/

def or1 : List Q(Prop) → Q(Prop)
  | [] => q(False)
  | [p] => q(p)
  | p::ps => q(p ∨ (← or1 ps))

def or2 : List Q(Prop) → Q(Prop)
  | [] => q(False)
  | p::ps => q(p ∨ (← or2 ps))

def orChange : (ps : List Q(Prop)) → Q((← or1 ps) → (← or2 ps))
  | [] => q(id)
  | [p] => by
    simp [or1, or2]
    exact q(Or.inl)
  | p::(ps1::ps2) => by
    have this : QQ _ := orChange (ps1::ps2)
    simp [or1, or2] at this ⊢
    revert this -- generalize only works in target
    generalize hx : or1 (ps1 :: ps2) = x
    generalize hy : or2 ps2 = y
    intro this
    exact q(by
      intro h
      cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (this h))
