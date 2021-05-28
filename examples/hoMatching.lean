import Qq
open Qq Lean

def turnExistsIntoForall : Q(Prop) → MetaM Q(Prop)
  | ~q(∃ x y, $p x y) => q(∀ x y, $p x y)
  | e => e

#eval turnExistsIntoForall q(∃ x y, String.length x ≤ y + 42)