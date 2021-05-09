import Qq
open Qq

set_option trace.compiler.ir.result true in
def betterApp {α : QQ Sort u} {β : QQ α → Sort v}
  (f : QQ (a : α) → β a) (a : QQ α) : QQ β a :=
qq f a

#eval betterApp (qq Int.toNat) (qq 42)