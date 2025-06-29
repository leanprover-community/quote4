import Qq.Macro
import Lean
/-!
# `run_tacq` and `by_elabq`

This file provides Qq analogues to `by_elab` and `run_tac`.
-/

namespace Qq
open Lean Meta Elab Tactic

/--
Build a let expression, similarly to `mkLetFVars`.
The array of `values` will be assigned to the current local context,
which is expected to consist of `cdecl`s.
-/
private def mkLetFVarsFromValues (values : Array Expr) (body : Expr) : MetaM Expr := do
  let ctx ← getLCtx
  let ctxLet := ctx.foldl (init := LocalContext.empty) fun part decl =>
    part.addDecl (.ldecl decl.index decl.fvarId decl.userName
      decl.type values[decl.index]! false decl.kind)
  let fvars : Array Expr := ctx.foldl (init := #[]) fun part decl =>
    part.push (.fvar decl.fvarId)
  withLCtx ctxLet #[] <| mkLetFVars fvars body

/--
`by_elabq` is the Qq analogue to `by_elab` which allows executing arbitrary `TermElabM` code in
place of a term. In contrast to `by_elab`, the local context can be directly accessed as quoted
expressions and the return type is Q-annotated.
Example:
```
def f (x : Prop) [Decidable x] : Int :=
  by_elabq
    Lean.logInfo x
    Lean.logInfo x.ty
    return q(if $x then 2 else 3)
```
See also: `run_tacq`.
-/
scoped
elab "by_elabq" e:doSeq : term <= expectedType => do
  let lctx ← getLCtx
  let levelNames ← Term.getLevelNames
  let (quotedCtx, assignments, quotedGoal) ← liftMetaM <| StateT.run'
        (s := { mayPostpone := false }) do
    let (quotedCtx, assignments) ← Impl.quoteLCtx lctx levelNames
    let quotedGoal : Q(Type) ←
      if expectedType.hasMVar then pure q(TermElabM Expr)
      else
        let expectedTypeQ : Q(Expr) ← Qq.Impl.quoteExpr expectedType
        pure <| q(TermElabM (Quoted $expectedTypeQ))
    return (quotedCtx, assignments, quotedGoal)
  let codeExpr : Expr ← withLCtx quotedCtx #[] do
    let body ← Term.elabTermEnsuringType (← `(do $e)) quotedGoal
    Term.synthesizeSyntheticMVarsNoPostponing
    let body ← instantiateMVars body
    if (← Term.logUnassignedUsingErrorInfos (← getMVars body)) then throwAbortTerm
    mkLetFVarsFromValues assignments body
  let code ← unsafe evalExpr (TermElabM Expr) q(TermElabM Expr) codeExpr
  code

/--
`run_tacq` is the Qq analogue to `run_tac` which allows executing arbitrary `TacticM` code.
In contrast to `run_tac`, the local context of the main goal can be directly accessed as quoted
expressions. Optionally, the annotated goal can also be saved using the syntax `run_tacq $g =>`.
Example:
```
example (a b : Nat) (h : a = b) : True := by
  run_tacq goal =>
    let p : Q(Prop) := q($a = $b)
    let t ← Lean.Meta.inferType h
    Lean.logInfo p
    Lean.logInfo <| toString (← Lean.Meta.isDefEq t p)
    Lean.logInfo <| toString (← Lean.Meta.isDefEq h.ty p)
    Lean.logInfo goal
    Lean.logInfo goal.ty
  trivial
```
See also: `by_elabq`.
-/
scoped syntax "run_tacq" (atomic(ident "=>"))? doSeq : tactic

elab_rules : tactic
| `(tactic| run_tacq $[$gi:ident =>]? $seq:doSeq) => do
  let goal ← try
    getMainGoal
  catch _ =>
    throwError "no open goal, run_tacq requires main goal"
  goal.withContext do
    let lctx ← getLCtx
    let levelNames := (← Term.getLevelNames).reverse -- these are backwards!
    let target ← instantiateMVars (← goal.getType)
    let (quotedCtx, assignments, goalInfo?) ← liftMetaM <| StateT.run'
          (s := { mayPostpone := false }) do
      let (quotedCtx, assignments) ← Impl.quoteLCtx lctx levelNames
      match gi with
      | none => return (quotedCtx, assignments, none)
      | some goalName =>
        let quotedTarget : Q(Expr) ← Qq.Impl.quoteExpr target
        let goalFid ← mkFreshFVarId
        let quotedCtx := quotedCtx.mkLocalDecl goalFid goalName.getId
          q(Quoted $quotedTarget) .default
        let assignments := assignments.push (toExpr (Expr.mvar goal))
        return (quotedCtx, assignments, some (goalName, goalFid))
    let codeExpr : Expr ← withLCtx quotedCtx #[] do
      if let .some (goalName, goalFid) := goalInfo? then
        discard <| Term.addTermInfo' (isBinder := true) goalName (Expr.fvar goalFid)
      let body ← Term.elabTermEnsuringType (← `(discard do $seq)) q(TacticM Unit)
      Term.synthesizeSyntheticMVarsNoPostponing
      let body ← instantiateMVars body
      if (← Term.logUnassignedUsingErrorInfos (← getMVars body)) then throwAbortTerm
      mkLetFVarsFromValues assignments body
    let code ← unsafe evalExpr (TacticM Unit) q(TacticM Unit) codeExpr
    code

end Qq
