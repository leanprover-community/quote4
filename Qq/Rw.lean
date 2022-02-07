import Qq.Macro
-- import Qq.Delab
open Lean Meta

namespace Qq

namespace Impl

@[specialize]
partial def recurse (f : Expr → MetaM (Option Expr)) (e : Expr) : MetaM Expr := do
  if let some e' ← f e then
    return e'
  match e with
  | Expr.app _ _ _ => return mkAppN e.getAppFn (← e.getAppArgs.mapM (recurse f))
  | Expr.lam n t e d =>
    let t ← recurse f t
    withLocalDecl n d.binderInfo t fun x => do
      mkLambdaFVars #[x] <| ← recurse f (e.instantiate #[x])
  | Expr.forallE n t e d =>
    let t ← recurse f t
    withLocalDecl n d.binderInfo t fun x => do
      mkForallFVars #[x] <| ← recurse f (e.instantiate #[x])
  | Expr.letE n t v e d =>
    let t ← recurse f t
    let v ← recurse f v
    withLetDecl n t v fun x => do
      mkLetFVars #[x] <| ← recurse f (e.instantiate #[x])
  | Expr.mdata md e _ => return mkMData md (← recurse f e)
  | Expr.proj n i e _ => return mkProj n i (← recurse f e)
  | e => return e

def qrwInside (a b : Expr) : Expr → MetaM Expr :=
  recurse fun e => do
    -- if ← withNewMCtxDepth <| withReducible <| isDefEq a e then return b
    if a == e then return b
    return none

def qrwE (s : UnquoteState) (a b : Expr) : Expr → MetaM Expr :=
  recurse fun e => do
    if e.isAppOfArity ``QQ 1 then
      return ← StateT.run' (s := s) do
        let t ← unquoteExpr (e.getArg! 0)
        let t ← qrwInside a b t
        return mkApp (mkConst ``QQ) (← quoteExpr t (← get))
    return none

def qrwLCtx (s : UnquoteState) (a b : Expr) : MetaM LocalContext := do
  let mut i := 0
  for fv in (collectFVars (collectFVars {} a) b).fvarSet do
    if let some ldecl := (← getLCtx).find? fv then
      i := i.max (ldecl.index + 1)
  let mut lctx' : LocalContext := {}
  for ldecl in ← getLCtx do
    if ldecl.index < i then
      lctx' := lctx'.addDecl ldecl
    else
      lctx' := lctx'.addDecl <| ← withLCtx lctx' (← determineLocalInstances lctx') do
        return ldecl.setType (← qrwE s a b ldecl.type)
  return lctx'

end Impl

open Impl Elab Term in
elab "qrw" eq:incQuotDepth(term) ";" e:term : term <= expectedType => do
  tryPostponeIfMVar expectedType
  unless eq matches `($a = $b) do throwErrorAt eq "not an equality"
  let (_, s) ← unquoteLCtx.run {}
  let eq ← withLCtx s.unquoted (← determineLocalInstances s.unquoted) do
    let (eq, lifts) ← floatExprAntiquot 0 eq #[]
    for (_, _, lift) in lifts do
      throwErrorAt lift "complex antiquotation not supported in qrw"
    elabTerm eq none
  synthesizeSyntheticMVarsNoPostponing
  let eq ← instantiateMVars eq
  let a := eq.getArg! 1
  let b := eq.getArg! 2
  let expectedType ← qrwE s a b expectedType
  let lctx ← qrwLCtx s a b
  withLCtx lctx (← determineLocalInstances lctx) do
    elabTerm e expectedType

