import Qq.MetaM

/-!
# Qq integration for `simproc`s

This file adds wrappers for operations relating to `simproc`s in the `Lean.Meta.Simp` namespace.

It can be used as
```lean
simproc_decl some_proc (some_pattern) := Meta.Simp.Simproc.ofQ fun u α e => do
  sorry
```
instead of the usual
```lean
simproc_decl some_proc (some_pattern) := fun e => do
  sorry
```
-/

open Lean Qq

variable {u : Level} {α : Q(Sort u)}

namespace Lean.Meta.Simp

/-- A copy of `Meta.Simp.Result` with explicit types. -/
def ResultQ (_e : Q($α)) : Type := Lean.Meta.Simp.Result

/-- A copy of `Meta.Simp.Result.mk` with explicit types. -/
@[inline] def ResultQ.mk {e : Q($α)}
    (expr : Q($α))
    (proof? : Option Q($e = $expr))
    (cache : Bool := true) : ResultQ e :=
  {expr, proof?, cache}

/-- A copy of `Meta.Simp.Step` with explicit types. -/
def StepQ (_e : Q($α)) : Type := Step

@[inherit_doc Step.done, inline]
def StepQ.done {e : Q($α)} (r : ResultQ e) : StepQ e := Step.done r
@[inherit_doc Step.visit, inline]
def StepQ.visit {e : Q($α)} (r : ResultQ e) : StepQ e := Step.visit r
@[inherit_doc Step.continue, inline]
def StepQ.continue {e : Q($α)} (r : Option (ResultQ e) := none) : StepQ e := Step.continue r

/-- A copy of `Lean.Meta.Simproc` with explicit types.

See `Simproc.ofQ` to construct terms of this type. -/
abbrev SimprocQ : Type := ∀ (u : Level) (α : Q(Sort u)) (e : Q($α)), Meta.SimpM (StepQ e)

/-- Build a simproc with Qq-enabled typechecking of inputs and outputs.

This calls `inferTypeQ` on the expression and passes the arguments to `proc`. -/
def Simproc.ofQ (proc : SimprocQ) : Simproc := fun e => do
  let ⟨u, α, e⟩ ← inferTypeQ e
  proc u α e

end Lean.Meta.Simp
