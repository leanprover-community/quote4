import Qq
open Qq

/-
  This fails, the second definition of `n`, which is not of type `Nat`, shadows the first, 
  `Nat`-typed, definition of `n`. 
  Even if the second definition is not available inside the quotation (`Nat → Nat` does not implement `ToExpr`)
  we don't want `$n` to refer to the shadowed definition, that would be confusing
-/
example : Q(Nat) :=
  let n : Nat := 1
  let n : Nat → Nat := fun _ => n
  q($n)