import Lean
open Lean Elab Meta Term

namespace Lean.Meta

open MetavarContext.MkBinding in
@[inline] def abstractRange' (xs : Array Expr) (i : Nat) (e : Expr) : M Expr := do
  let e ← MetavarContext.MkBinding.elimMVarDeps xs e
  pure (e.abstractRange i xs)

/-- Similar to `abstract`, but consider only the first `min n xs.size` entries in `xs`. -/
def abstractRange (e : Expr) (n : Nat) (xs : Array Expr) : MetaM Expr :=
  liftMkBindingM <| fun lctx => abstractRange' xs n e false

/-- Replace free variables `xs` with loose bound variables. -/
def abstract (e : Expr) (xs : Array Expr) : MetaM Expr :=
  abstractRange e xs.size xs

/-- Replace occurrences of the free variables `fvars` in `e` with `vs` -/
def replaceFVars (e : Expr) (fvars : Array Expr) (vs : Array Expr) : MetaM Expr := do
  (← abstract e fvars).instantiateRev vs