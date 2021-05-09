# Expression quotations for Lean 4

This package combines the
intuitiveness of modal sequent calculus
with the power and speed of
Lean 4's metaprogramming facilities.
It introduces the `QQ` modality:
`QQ α` denotes an expression of type `α`.
The type former comes with the following
natural introduction rule:

```
   α,    β,    γ ⊢    t : Type
------------------------------
QQ α, QQ β, QQ γ ⊢ QQ t : Type
```

The lower-case `qq` macro serves
as the modal inference rule,
allowing us to construct values in `qq α`:
```
   α,    β,    γ ⊢    t :    δ
------------------------------
QQ α, QQ β, QQ γ ⊢ qq t : QQ δ
```

## Example

Let us write a type-safe version of `mkApp`:

```lean
import Qq
open Qq

set_option trace.compiler.ir.result true in

def betterApp {α : QQ Sort u} {β : QQ α → Sort v}
  (f : QQ (a : α) → β a) (a : QQ α) : QQ β a :=
qq f a

#eval betterApp (qq Int.toNat) (qq 42)
```

There are many things going on here:
1. The `betterApp` function compiles to a single `mkApp` call.
1. It does not require the `MetaM` monad.
1. Implicit arguments (such as `α` or `u`) get filled in by type inference.
1. The second argument, `qq 42`,
   correctly constructs an expression of type `Int`.

Because `betterApp`
takes `α` and `u` (and `β` and `v`) as arguments,
it can also perform more interesting tasks:
for example,
we can change `qq f a` into `qq id f a`
without changing the interface
(even though the resulting expression
now contains both the type and the universe level).

The arguments do not need to refer
to concrete types like `Int` either:
`List ((u : Level) × (α : QQ Sort u) × List (QQ (Option α)))`
does what you think it does!

## Implementation

The type family on which this package is built is called `QQ'`:

```lean
structure QQ' (α : Expr) where
  quoted : Expr
```

The intended meaning of `⟨e⟩ : QQ' t` is that
`e` is an expression of type `t`.
Or if you will,
`isDefEq (← inferType e) t`.
(This invariant is not enforced though,
but it can be checked with `QQ'.check`.)
The `QQ'` type is almost impossible to use manually.
You should only interact with it
using the `qq` macro.

## Comparison

Template Haskell provides a similar mechanism
for type-safe quotations,
writing `Q Int` for an expression of type `Int`.
This is subtly different
to the `QQ'` type family considered here:
in Lean notation,
TH's family has the type `Q : Type u → Type`,
while ours has the type `QQ' : Expr → Type`.
In Lean, `Q` is not sufficiently expressive
due to universe polymorphism:
we might only know at runtime which universe the type is in,
but `Q` version fixes the universe at compile time.
Another lack of expressivity concerns dependent types:
a telescope such as `{α : Q Type} (a : Q α)` is not well-typed
with the `Q` constructor,
because `α` is not a type.

## To do

- This has almost certainly been done before
  somewhere else, by somebody else.

- Pattern matching.
  In a pure context,
  without access to `MetaM`,
  we can only match the expression literally.
  I don't think this is particularly useful,
  since e.g. type class arguments will
  typically require unfolding to match.

- `qq Type (← myLevelFun a)`.
  And maybe use `$` instead of `←`.

- When the local context contains a hypothesis
  like `qq (← frob a) ∨ b`,
  then `qq` will usually fail with
  `reduceEval: failed to evaluate argument (frob a).1`.
  The case `a.1` is already supported,
  it could be enough to generalize the subterm in the hypothesis.

- Auto-bound implicit types
  send Lean into an infinite loop
  (not universes though).

- `by exact qq _` does not produce an error
  (and you don't get to see the type of the underscore).

- Integration with `MetaM`,
  such as an `inferType` variant
  returning a quote.

- Other bug fixes, documentation, and assorted polishing.
