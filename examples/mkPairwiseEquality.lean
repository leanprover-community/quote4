import Qq
open Qq

def mkPairwiseEquality {α : QQ Sort u} : List (QQ α) → QQ Prop
  | [a, b] => qq a = b
  | a :: b :: cs => qq a = b ∧ (← mkPairwiseEquality (b :: cs))
  | _ => qq True