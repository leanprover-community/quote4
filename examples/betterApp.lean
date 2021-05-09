import Qq
open Qq

set_option trace.compiler.ir.result true in

def betterApp {α : Q(Sort u)} {β : Q(α → Sort v)}
  (f : Q((a : α) → β a)) (a : Q(α)) : Q(β a) :=
q(f a)

#eval betterApp q(Int.toNat) q(42)