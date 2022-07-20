# Expression quotations for Lean 4

This package implements type-safe expression
quotations, which are a particularly
convenient way of constructing object-level
expressions (`Expr`) in meta-level code.

It combines the intuitiveness of modal sequent
calculus with the power and speed of
Lean 4's metaprogramming facilities.
The `Q(·)` modality quotes types:
`Q(α)` denotes an expression of type `α`.
The type former comes with the following
natural introduction rule:

```
$a₁ :   α₁,   …,  $aₙ :   αₙ   ⊢    t  : Type
---------------------------------------------
 a₁ : Q(α₁),  …,   aₙ : Q(αₙ)  ⊢  Q(t) : Type
```

The lower-case `q(·)` macro serves
as the modal inference rule,
allowing us to construct values in `Q(·)`:
```
$a₁ :   α₁,   …,  $aₙ :   αₙ   ⊢    t  :   β
---------------------------------------------
 a₁ : Q(α₁),  …,   aₙ : Q(αₙ)  ⊢  q(t) : Q(β)
```

## Example

Let us write a type-safe version of `mkApp`:

```lean
import Qq
open Qq

set_option trace.compiler.ir.result true in

-- Note: `betterApp` actually has two additional parameters
-- `{u v : Lean.Level}` auto-generated due to option
-- `autoBoundImplicitLocal`.

def betterApp {α : Q(Sort u)} {β : Q($α → Sort v)}
  (f : Q((a : α) → $β a)) (a : Q($α)) : Q($β $a) :=
q($f $a)

#eval betterApp q(Int.toNat) q(42)
```

There are many things going on here:
1. The `betterApp` function compiles to a single `betaRev` call.
1. It does not require the `MetaM` monad (in contrast to
   `AppBuilder.lean` in the Lean 4 code).
1. `Q(…)` is definitionally equal to `Expr`, so each variable
   in the example is just an `Expr`.
1. Nevertheless, implicit arguments of the definition (such as `α`
   or `u`) get filled in by type inference, which reduces the
   potential for errors even in the absence of strong type safety
   at the meta level.
1. All quoted expressions, i.e. all code inside `Q(·)` and `q(·)`,
   are type-safe (under the assumption that the values of `α`,
   `f`, etc. really have their declared types).
1. The second argument in the `#eval` example, `q(42)`,
   correctly constructs an expression of type `Int`, as
   determined by the first argument.

Because `betterApp`
takes `α` and `u` (and `β` and `v`) as arguments,
it can also perform more interesting tasks compared
to the untyped function `mkApp`: for example,
we can change `q($f $a)` into `q(id $f $a)`
without changing the interface
(even though the resulting expression
now contains both the type and the universe level).

The arguments do not need to refer
to concrete types like `Int` either:
`List ((u : Level) × (α : Q(Sort u)) × List Q(Option $α))`
does what you think it does!

In fact it is a crucial feature
that we can write metaprograms
transforming terms of nonconcrete types
in inconsistent contexts:
```lean
def tryProve (n : Q(Nat)) (i : Q(Fin $n)) : Option Q($i > 0) := ...
```
If the `i > 0` in the return type were a concrete type in the metalanguage,
then we could not call `tryProve` with `n := 0`
(because we would need to provide a value for `i : Fin 0`).
Furthermore,
if `n` were a concrete value,
then we could not call `tryProve` on
the subterm `t` of `fun n : Nat => t`.

## Implementation

The type family on which this package is built is called `QQ`:

```lean
def QQ (α : Expr) := Expr
```

The intended meaning of `e : QQ t` is that
`e` is an expression of type `t`.
Or if you will,
`isDefEq (← inferType e) t`.
(This invariant is not enforced though,
but it can be checked with `QQ.check`.)
The `QQ` type is not meant to be used manually.
You should only interact with it
using the `Q(·)` and `q(·)` macros.

## Comparison

Template Haskell provides a similar mechanism
for type-safe quotations,
writing `Q Int` for an expression of type `Int`.
This is subtly different
to the `QQ` type family considered here:
in Lean notation,
TH's family has the type `Q : Type u → Type`,
while ours has the type `QQ : Expr → Type`.
In Lean, `Q` is not sufficiently expressive
due to universe polymorphism:
we might only know at runtime which universe the type is in,
but `Q` version fixes the universe at compile time.
Another lack of expressivity concerns dependent types:
a telescope such as `{α : Q Type} (a : Q α)` is not well-typed
with TH's `Q` constructor,
because `α` is not a type.

## To do

- This has almost certainly been done before
  somewhere else, by somebody else.

- `ql(imax u (v+1))`

- Automatically create free variables for recursion.
  Maybe something like this:
```lean
def turnExistsIntoForall : Q(Prop) → MetaM Q(Prop)
  | ~q(∃ x, p x) => do
     q(∀ x, $(x => turnExistsIntoForall q($p $x)))
  | e => e
```

- Matching should provide control over type-class diamonds, such as
```lean
~q((a + b : α) where
  Semiring α
  commutes ∀ n, OfNat α n
  a + a defEq 0)
```

- Matching on types should be possible, that is,
  `match (e : Expr) with | ~q($p ∧ $q) => ...`.

- Other bug fixes, documentation, and assorted polishing.
