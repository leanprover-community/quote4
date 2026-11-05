/-
Copyright (c) 2026 Lean FRO, LLC and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dionisio Chiuratto Agourakis
-/
import Qq

open Qq Lean.Meta

/-!
Regression tests for https://github.com/leanprover-community/quote4/issues/30

The universe level of the discriminant's type was left as an unassigned metavariable
(`Quoted` is `implicit_reducible`, so elaborating the discriminant never constrains it),
and it survived into the `match_eq` hypothesis generated for the `~q` pattern. Any nested
`match` (or a multi-discriminant `match` with the `~q` pattern in a non-final position)
then failed with "type of pattern variable 'match_eq✝' contains metavariables".
-/

/-- The issue's MWE: a `~q` match whose branch contains another `match`. -/
example (qo : Q(Option Nat)) (o : Option Nat) : MetaM Unit := do
  match qo with
  | ~q(some $qx) => match o with
    | some _ => pure ()
    | _ => pure ()
  | _ => pure ()

/-- 0art0's variant from the issue discussion: the `~q` pattern is not in the last
discriminant position. This failed with "type of pattern variable 'match_eq✝' contains
metavariables". -/
def matchQPropFirst : (P : Q(Prop)) → (args : List Nat) → MetaM String
  | ~q($A ∧ $B), [] => return "and"
  | _, _ => return "other"

/-- Control: the argument order that already worked before the fix. -/
def matchQPropLast : (args : List Nat) → (P : Q(Prop)) → MetaM String
  | [], ~q($A ∧ $B) => return "and"
  | _, _ => return "other"

/-- The matched functions still compute as expected. -/
def exAnd : Q(Prop) := q(True ∧ True)

/-- info: "and" -/
#guard_msgs in
#eval show MetaM _ from matchQPropFirst exAnd []

/-- info: "other" -/
#guard_msgs in
#eval show MetaM _ from matchQPropFirst q(True) [1]

/-- info: "and" -/
#guard_msgs in
#eval show MetaM _ from matchQPropLast [] exAnd
