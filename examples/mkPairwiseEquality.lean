import Quote
open Quote

def mkPairwiseEquality {α : quote Sort u} : List (quote α) → quote Prop
  | [a, b] => quote a = b
  | a :: b :: cs => quote a = b ∧ (← mkPairwiseEquality (b :: cs))
  | _ => quote True