
import Lean
import Qq

open Lean Meta
open Qq

set_option pp.macroStack true in
def foo₁ (T : Q(Type)) : MetaM Bool := do
  if let ~q(Prop) := T then
    let x := Nat.zero.succ
    return (Nat.zero, ()).2
  return true


set_option pp.macroStack true in
set_option pp.rawOnError true in
def foo₂ (T : Q(Type)) : MetaM Bool := do
  let x : Unit ← match T with
    | ~q(Prop) => return true || true
    | ~q(Nat) => return true == true
    | _ => return true && true
  pure false

#eval show MetaM Unit from do
  let x :=
    pure ()
    pure Nat.zero
  pure ()


#eval foo₂ q(Prop)
#eval foo₂ q(Int)


#print foo₁
#print foo₂


set_option pp.macroStack true in
def afoo₁ (T : Q(Type)) : MetaM Bool := do
  if let some (x : Nat) := none then
    return false
  return true


set_option pp.macroStack true in
def afoo₂ (T : Q(Type)) : MetaM Bool := do
  let some (x : Nat) := none | return true
  return false

#print afoo₁
#print afoo₂
