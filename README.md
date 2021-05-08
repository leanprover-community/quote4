# Expression quotations for Lean 4

This package combines the
intuitiveness of modal sequent calculus
with the power and speed of
Lean 4's metaprogramming facilities.
It introduces the `quote` modality:
`quote α` denotes an expression of type `α`.
The type former comes with the following
natural introduction rule:

```
      α,       β,       γ ⊢       t : Type
------------------------------------------
quote α, quote β, quote γ ⊢ quote t : Type
```

The `quote` macro also serves
as the modal inference rule,
allowing us to construct values in `quote α`:
```
      α,       β,       γ ⊢       t :       δ
---------------------------------------------
quote α, quote β, quote γ ⊢ quote t : quote δ
```

## Example

Let us write a type-safe version of `mkApp`:

```lean
import Quote
open Quote

set_option trace.compiler.ir.result true in

def betterApp {α : quote Sort u} {β : quote α → Sort v}
  (f : quote (a : α) → β a) (a : quote α) : quote β a :=
quote f a

#eval betterApp (quote Int.toNat) (quote 42)
```

There are many things going on here:
1. The `betterApp` function compiles to a single `mkApp` call.
1. It does not require the `MetaM` monad.
1. Implicit arguments (such as `α` or `u`) get filled in by type inference.
1. The second argument, `quote 42`,
   correctly constructs an expression of type `Int`.

Because `betterApp`
takes `α` and `u` (and `β` and `v`) as arguments,
it can also perform more interesting tasks:
for example,
we can change `quote f a` into `quote id f a`
without changing the interface
(even though the resulting expression
now contains both the type and the universe level).

The arguments do not need to refer
to concrete types like `Int` either:
`List ((u : Level) × (α : quote Sort u) × List (quote (Option α)))`
does what you think it does!

## Implementation

The type family on which this package is built is called `QQ`:

```lean
structure QQ (α : Expr) where
  quoted : Expr
```

The intended meaning of `⟨e⟩ : QQ t` is that
`e` is an expression of type `t`.
Or if you will,
`isDefEq (← inferType e) t`.
(This invariant is not enforced though,
but it can be checked with `QQ.check`.)
The `QQ` type is almost impossible to use manually.
You should only interact with it
using the `quote` macro.

## To do

- This has almost certainly been done before
  somewhere else, by somebody else.

- Pick another name.
  There is already a `Lean.Quote` type,
  which means something slightly different.

- Pattern matching.
  In a pure context,
  without access to `MetaM`,
  we can only match the expression literally.
  I don't think this is particularly useful,
  since e.g. type class arguments will
  typically require unfolding to match.

- `quote (← frob a) ∨ b`.
  For now, `let fa := frob a; quote fa ∨ b`
  is a reasonable workaround.

- When the local context contains a hypothesis
  like `h : let fa := frob a; quote fa ∨ b`,
  then `quote` will usually fail with
  `reduceEval: failed to evaluate argument (frob a).1`.
  The case `a.1` is already supported,
  it could be enough to generalize the subterm in the hypothesis.

- Auto-bound implicit types
  send Lean into an infinite loop
  (not universes though).

- `by exact quote _` does not produce an error
  (and you don't get to see the type of the underscore).

- Integration with `MetaM`,
  such as an `inferType` variant
  returning a quote.

- Other bug fixes, documentation, and assorted polishing.
