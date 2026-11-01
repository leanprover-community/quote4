import Qq

/-!
Regression tests for https://github.com/leanprover-community/quote4/issues/126

`q(·)` postpones its own elaboration while the local context contains
metavariables, which routinely happens inside nested `~q` matches. The postponed
work used to be synthesized only after the match code had been generated, so the
compiled declaration ended up containing metavariables and was rejected by the
kernel with `declaration has metavariables`. Both definitions below failed with
that error before the fix; compiling them is the test.
-/

open Qq Lean

opaque Foo {α β : Type} (f : α → β) : Prop

opaque someProp : Q(Prop)

set_option linter.unusedVariables false in
/-- Nested `~q` matches with a quotation in the innermost body (no recursion). -/
def nestedMatchQuotation {α β : Q(Type)} (f : Q($α → $β)) : MetaM Q(Foo $f) := do
  match β with
  | ~q(Nat) => failure
  | ~q(Int) =>
    let t : Q(Prop) := someProp
    let ~q(@Foo $α'' $β'' $f'') := t | failure
    let _x := q($f)
    failure

set_option linter.unusedVariables false in
/-- The shape from the original report: a `partial` recursive definition. -/
partial def proveFoo {α β : Q(Type)} (f : Q($α → $β)) : MetaM Q(Foo $f) := do
  match β with
  | ~q(Nat) => failure
  | ~q(Int) =>
    let t : Q(Prop) := someProp
    let ~q(@Foo $α'' $β'' $f'') := t | failure
    let pf : Q(Foo $f) ← proveFoo q($f)
    failure
