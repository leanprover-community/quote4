import Quote
open Quote

/-!
Type-safe conversion from proofs of `a ∨ b` to proofs of `a ∨ b ∨ false`.
-/

def or1 : List (quote Prop) → quote Prop
  | [] => quote False
  | [p] => quote p
  | p::ps =>
    let ps' := or1 ps
    quote p ∨ ps'

def or2 : List (quote Prop) → quote Prop
  | [] => quote False
  | p::ps =>
    let ps' := or2 ps
    quote p ∨ ps'

theorem Or.elim {c : Prop} {a b : Prop} (h : a ∨ b) (h1 : a → c) (h2 : b → c) : c := by
  induction h
  apply h1; assumption
  apply h2; assumption

def orChange :
    (ps : List (quote Prop)) →
      let ps1 := or1 ps
      let ps2 := or2 ps
      quote ps1 → ps2
  | [] => quote id
  | [p] => by
    simp [or1, or2]
    exact quote Or.inl
  | p::(ps1::ps2) => by
    have this : QQ _ := orChange (ps1::ps2)
    simp [or1, or2] at this ⊢
    revert this -- generalize only works in target
    generalize hx : or1 (ps1 :: ps2) = x
    generalize hy : or2 ps2 = y
    intro this
    exact quote fun h => h.elim Or.inl (fun p => Or.inr (this p))
