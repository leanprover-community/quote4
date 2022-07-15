import Lean
open Lean Meta

namespace Lean.Meta

def throwFailedToEval (e : Expr) : MetaM α :=
  throwError "reduceEval: failed to evaluate argument{indentExpr e}"

private partial def evalList [ReduceEval α] (e : Expr) : MetaM (List α) := do
  let e ← whnf e
  let .const c _ ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``List.nil, 1 => pure []
    | ``List.cons, 3 => return (← reduceEval (e.getArg! 1)) :: (← evalList (e.getArg! 2))
    | _, _ => throwFailedToEval e

instance [ReduceEval α] : ReduceEval (List α) := ⟨evalList⟩

instance : ReduceEval (Fin (n+1)) where
  reduceEval := fun e => do
    let e ← whnf e
    if e.isAppOfArity ``Fin.mk 3 then
      return Fin.ofNat (← reduceEval (e.getArg! 1))
    else
      throwFailedToEval e

instance : ReduceEval UInt64 where
  reduceEval := fun e => do
    let e ← whnf e
    if e.isAppOfArity ``UInt64.mk 1 then
      let _ : ReduceEval (Fin UInt64.size) := instReduceEvalFinHAddNatInstHAddInstAddNatOfNat
      pure ⟨(← reduceEval (e.getArg! 0))⟩
    else
      throwFailedToEval e

instance : ReduceEval USize where
  reduceEval := fun e => do
    let e ← whnf e
    if e.isAppOfArity ``USize.mk 1 then
      let a ← whnf (e.getArg! 0)
      if a.isAppOfArity ``Fin.mk 3 then
        return USize.ofNat (← reduceEval (a.getArg! 1))
    throwFailedToEval e

instance : ReduceEval Bool where
  reduceEval := fun e => do
    let e ← whnf e
    if e.isAppOf ``true then
      pure true
    else if e.isAppOf ``false then
      pure false
    else
      throwFailedToEval e

instance : ReduceEval BinderInfo where
  reduceEval := fun e => do
    match (← whnf e).constName? with
    | some ``BinderInfo.default => pure .default
    | some ``BinderInfo.implicit => pure .implicit
    | some ``BinderInfo.strictImplicit => pure .strictImplicit
    | some ``BinderInfo.instImplicit => pure .instImplicit
    | some ``BinderInfo.auxDecl => pure .auxDecl
    | _ => throwFailedToEval e

instance : ReduceEval Literal where
  reduceEval := fun e => do
    let e ← whnf e
    if e.isAppOfArity ``Literal.natVal 1 then
      return .natVal (← reduceEval (e.getArg! 0))
    else if e.isAppOfArity ``Literal.strVal 1 then
      return .strVal (← reduceEval (e.getArg! 0))
    else
      throwFailedToEval e

instance : ReduceEval MVarId where
  reduceEval e := do
    let e ← whnf e
    if e.isAppOfArity ``MVarId.mk 1 then
      return ⟨← reduceEval (e.getArg! 0)⟩
    else
      throwFailedToEval e

instance : ReduceEval FVarId where
  reduceEval e := do
    let e ← whnf e
    if e.isAppOfArity ``FVarId.mk 1 then
      return ⟨← reduceEval (e.getArg! 0)⟩
    else
      throwFailedToEval e
