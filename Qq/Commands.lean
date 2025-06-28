import Qq.Macro
import Lean

namespace Qq
open Lean Meta Elab Tactic

private
def mkHaveFVars (assignments : Array Expr) (body : Expr) : MetaM Expr := do
  let ctx ← getLCtx
  let (_, res) ← ctx.foldrM (init := (assignments, body)) fun decl (assignments, body) => do
    let value := assignments.back!
    let result := .letE decl.userName decl.type value (body.abstract #[.fvar decl.fvarId]) false
    return (assignments.pop, result)
  return res

/--
`by_elabq` is the Qq analogue to `by_elab`
Executes arbitrary `TermElabM` code in place of a term.
Moreover, all variables available in the local context are accessible as
quoted expressions, and the return value is Q-annotated as well.
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
        (s := {mayPostpone := False}) do
    let (quotedCtx, assignments) ← Impl.quoteLCtx lctx levelNames
    let quotedGoal : Q(Type) ←
      if expectedType.isMVar then pure q(TermElabM Expr)
      else
        let expectedTypeQ : Q(Expr) ← Qq.Impl.quoteExpr expectedType
        pure <| q(TermElabM (Quoted $expectedTypeQ))
    return (quotedCtx, assignments, quotedGoal)
  let codeExpr : Expr ← withLCtx quotedCtx #[] do
    let body ← Term.elabTermAndSynthesize (← `(do $e)) quotedGoal
    mkHaveFVars assignments body
  let code ← unsafe evalExpr (TermElabM Expr) q(TermElabM Expr) codeExpr
  code

/--
`run_tacq` is a Qq-analogue to `run_tac`
Executes an arbitrary `TacticM` code. Moreover, the local
context can be directly accessed as quoted expressions,
and the Q-annotated goal is available as `goalq`.
Example:
```
example (a b : Nat) (h : a = b) : True := by
  run_tacq
    let p : Q(Prop) := q($a = $b)
    let t ← Lean.Meta.inferType h
    Lean.logInfo p
    Lean.logInfo <| toString (← Lean.Meta.isDefEq t p)
    Lean.logInfo <| toString (← Lean.Meta.isDefEq h.ty p)
    Lean.logInfo goalq
    Lean.logInfo goalq.ty
  trivial
```
See also: `by_elabq`.
-/
scoped
elab "run_tacq" e:doSeq : tactic => do
  let goal ← try
    getMainGoal
  catch _ =>
    throwError "no open goal, run_tacq requires main goal"
  withMainContext do
    let goalName := `goalq
    let lctx ← getLCtx
    let levelNames ← Term.getLevelNames
    let target ← getMainTarget
    let (quotedCtx, assignments) ← liftMetaM <| StateT.run'
          (s := {mayPostpone := False}) do
      let (quotedCtx, assignments) ← Impl.quoteLCtx lctx levelNames
      let quotedTarget ← Qq.Impl.quoteExpr target
      let goalFid ← mkFreshFVarId
      let quotedCtx := quotedCtx.mkLocalDecl goalFid goalName
        (mkApp (mkConst ``Quoted) quotedTarget) .default
      let assignments := assignments.push (toExpr (Expr.mvar goal))
      return (quotedCtx, assignments)
    let codeExpr : Expr ← withLCtx quotedCtx #[] do
      let body ← Term.elabTermAndSynthesize (← `(discard do $e)) q(TacticM Unit)
      mkHaveFVars assignments body
    let typeExpr := q(TacticM Unit)
    let code ← unsafe evalExpr (TacticM Unit) typeExpr codeExpr
    code

end Qq
