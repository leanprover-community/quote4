import Qq
open Qq Lean

def turnExistsIntoForall : Q(Prop) → MetaM Q(Prop)
  | ~q(∃ x y, $p x y) => return q(∀ x y, $p x y)
  | e => return e

#eval turnExistsIntoForall q(∃ x y, String.length x ≤ y + 42)
