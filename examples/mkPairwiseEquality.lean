import Quote
open Quote

def mkPairwiseEquality {α : quote Sort u} : List (quote α) → quote Prop
  | [a, b] => quote a = b
  | a :: b :: cs =>
    let bEqCs := mkPairwiseEquality (b :: cs)
    quote a = b ∧ bEqCs
  | _ => quote True