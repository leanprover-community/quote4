import Qq
open Qq

example {α : Q(Sort u)} (a : Q($α)) : Unit :=
  have : u =QL 1 := ⟨⟩
  have : $α =Q Nat := ⟨⟩
  have : $a =Q 42 := ⟨⟩
  by exact -- TODO
  have : Q($a > 10) := q(by decide)
  ()