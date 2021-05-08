import Quote
open Quote

set_option trace.compiler.ir.result true in
def betterApp {α : quote Sort u} {β : quote α → Sort v}
  (f : quote (a : α) → β a) (a : quote α) : quote β a :=
quote f a

#eval betterApp (quote Int.toNat) (quote 42)