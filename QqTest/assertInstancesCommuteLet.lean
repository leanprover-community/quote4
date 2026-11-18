import Qq

open Qq Lean Meta

/-!
Regression tests for https://github.com/leanprover-community/quote4/issues/38

`assertInstancesCommute` used to loop (`maximum recursion depth reached`) when a
let-bound copy of a local instance was in scope (as produced by `let := x` or
`let _ ← …` in a `do` block): the redundant-instance finder picked the let-bound
alias as the canonical instance, the generated `QuotedDefEq` hypothesis then
degenerated (the alias unfolds during the next unquoting round), the
zeta-reduction that would eliminate the redundant instance never happened, and
the same instance was "rediscovered" forever.
-/

-- The MWE from the issue (plp127): an anonymous `let` copy of the instance.
example {α : Q(Type)} (x : Q(Inhabited $α)) : MetaM Unit := do
  let := x
  assertInstancesCommute
  pure ()

-- The original report's shape: several unnamed assumptions.
example {α : Q(Type)} (x : Q(Inhabited $α)) : MetaM Unit := do
  let := x
  let := x
  assertInstancesCommute
  pure ()

-- thorimur's MWE from the issue discussion: a named let-bound instance.
example {P : Q(Prop)} : MetaM Unit := do
  let _x := ← synthInstanceQ q(Decidable $P)
  assertInstancesCommute
  pure ()

-- The intended use still works: two independent instances of the same class
-- are recognized as redundant and discharged with a `QuotedDefEq` hypothesis.
example {α : Q(Type)} (x y : Q(Inhabited $α)) : MetaM Unit := do
  assertInstancesCommute
  pure ()

-- And `assumeInstancesCommute` behaves the same way around let-bound copies.
example {α : Q(Type)} (x : Q(Inhabited $α)) : MetaM Unit := do
  let := x
  assumeInstancesCommute
  pure ()
