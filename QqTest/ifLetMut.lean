import Qq
open Qq Lean

-- The MWE from https://github.com/leanprover-community/quote4/issues/36.
example : MetaM Nat := do
  let mut x := 1
  if let ~q(Prop) := q(Type) then
    x := 2
  else
    x := 3
  return x

/-- info: 3 -/
#guard_msgs in
#eval show MetaM Nat from do
  let mut x := 1
  if let ~q(Prop) := q(Type) then
    x := 2
  else
    x := 3
  return x

/-- info: 2 -/
#guard_msgs in
#eval show MetaM Nat from do
  let mut x := 1
  if let ~q(Prop) := q(Prop) then
    x := 2
  else
    x := 3
  return x

/-- info: 1 -/
#guard_msgs in
#eval show MetaM Nat from do
  let mut x := 1
  if let ~q(Prop) := q(Type) then
    x := 2
  return x

/-- info: 2 -/
#guard_msgs in
#eval show MetaM Nat from do
  let mut x := 1
  if let ~q(Prop) := q(Prop) then
    x := 2
  return x

example : Lean.Elab.Tactic.TacticM Nat := do
  let mut x := 1
  if let ~q(Prop) := q(Prop) then
    x := 2
  else
    x := 3
  return x

-- Capture-bearing patterns continue to use the existing continuation-based matcher.
example : MetaM Q(Nat) := do
  if let ~q($a) := q(1) then
    return a
  else
    return q(2)
