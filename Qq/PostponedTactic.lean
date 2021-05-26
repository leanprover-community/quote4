import Lean
open Lean Meta Elab Term

namespace Qq.Impl

def mkCIdentRaw (id : Name) : Syntax :=
  Syntax.ident (SourceInfo.fromRef Syntax.missing) (toString id).toSubstring id [(id, [])]

scoped elab "postponedTactic" mvarId:ident tac:tactic : term => do
  let mvarId := mvarId.getId
  modifyThe Meta.State fun s => { s with mctx := s.mctx.instantiateMVarDeclMVars mvarId }
  withMVarContext mvarId do
    if (← inferType (mkMVar mvarId)).hasExprMVar then
      -- dbg_trace "postponing {← instantiateMVars (← inferType (mkMVar mvarId))}"
      tryPostpone
    for decl in ← getLCtx do
      if decl.hasExprMVar then
        -- dbg_trace "postponing {(← instantiateLocalDeclMVars decl).type}"
        tryPostpone
    runTactic mvarId tac
    instantiateMVars (mkMVar mvarId)

def withPostponedTactics [Monad m] [MonadStateOf Term.State m] [MonadFinally m] [MonadRef m] [MonadQuotation m]
    (k : m α) : m α := do
  let s0 ← get
  set { s0 with syntheticMVars := [] }
  try k finally
    let s ← get
    set { s with syntheticMVars := s0.syntheticMVars ++ (← s.syntheticMVars.mapM fun mvar =>
      open SyntheticMVarKind in do match mvar.kind with
        | tactic tac ctx => ({ mvar with
            stx := (← `(postponedTactic $(mkCIdentRaw mvar.mvarId) $tac))
            kind := postponed ctx })
        | _ => mvar) }
