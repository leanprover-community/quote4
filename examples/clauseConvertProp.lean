import Qq
open Qq

/-!
Type-safe conversion from proofs of `a ∨ b` to proofs of `a ∨ b ∨ false`.
-/

def or1 : List (QQ Prop) → QQ Prop
  | [] => qq False
  | [p] => qq p
  | p::ps => qq p ∨ (← or1 ps)

def or2 : List (QQ Prop) → QQ Prop
  | [] => qq False
  | p::ps => qq p ∨ (← or2 ps)

theorem Or.elim {c : Prop} {a b : Prop} (h : a ∨ b) (h1 : a → c) (h2 : b → c) : c := by
  induction h
  apply h1; assumption
  apply h2; assumption

def orChange : (ps : List (QQ Prop)) → QQ (← or1 ps) → (← or2 ps)
  | [] => qq id
  | [p] => by
    simp [or1, or2]
    exact qq Or.inl
  | p::(ps1::ps2) => by
    have this : QQ' _ := orChange (ps1::ps2)
    simp [or1, or2] at this ⊢
    revert this -- generalize only works in target
    generalize hx : or1 (ps1 :: ps2) = x
    generalize hy : or2 ps2 = y
    intro this
    exact qq fun h => h.elim Or.inl (fun p => Or.inr (this p))
