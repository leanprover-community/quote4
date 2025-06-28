import Qq.Macro
import Lean

namespace Qq
open Lean Meta Elab Tactic

private
def mkLetFVarsFromValues (values : Array Expr) (body : Expr) : MetaM Expr := do
  let ctx ← getLCtx
  let ctxLet := ctx.foldl (init := LocalContext.empty) (fun part decl =>
    part.addDecl (.ldecl decl.index decl.fvarId decl.userName
      decl.type values[decl.index]! false decl.kind))
  let fvars : Array Expr := ctx.foldl (init := #[]) (fun part decl =>
    part.push (.fvar decl.fvarId))
  withLCtx ctxLet #[] do
    mkLetFVars fvars body

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
    mkLetFVarsFromValues assignments body
  let code ← unsafe evalExpr (TermElabM Expr) q(TermElabM Expr) codeExpr
  code

/--
`run_tacq` is a Qq-analogue to `run_tac`
Executes an arbitrary `TacticM` code. Moreover, the local
context can be directly accessed as quoted expressions.
Optionally, user can also save the annotated goal using
syntax `run_tacq $g =>`
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
scoped
syntax "run_tacq" ident "=>" doSeq : tactic
syntax "run_tacq" doSeq : tactic

def runTacq (gi : Option Name) (seq : TSyntax `Lean.Parser.Term.doSeq) : TacticM Unit := do
  let goal ← try
    getMainGoal
  catch _ =>
    throwError "no open goal, run_tacq requires main goal"
  withMainContext do
    let lctx ← getLCtx
    let levelNames ← Term.getLevelNames
    let target ← getMainTarget
    let (quotedCtx, assignments) ← liftMetaM <| StateT.run'
          (s := {mayPostpone := False}) do
      let (quotedCtx, assignments) ← Impl.quoteLCtx lctx levelNames
      match gi with
      | none => return (quotedCtx, assignments)
      | some goalName =>
        let quotedTarget ← Qq.Impl.quoteExpr target
        let goalFid ← mkFreshFVarId
        let quotedCtx := quotedCtx.mkLocalDecl goalFid goalName
          (mkApp (mkConst ``Quoted) quotedTarget) .default
        let assignments := assignments.push (toExpr (Expr.mvar goal))
        return (quotedCtx, assignments)
    let codeExpr : Expr ← withLCtx quotedCtx #[] do
      let body ← Term.elabTermAndSynthesize (← `(discard do $seq)) q(TacticM Unit)
      mkLetFVarsFromValues assignments body
    let code ← unsafe evalExpr (TacticM Unit) q(TacticM Unit) codeExpr
    code

elab_rules : tactic
| `(tactic| run_tacq $gi:ident => $seq:doSeq) => do
  runTacq gi.getId seq
| `(tactic| run_tacq $seq:doSeq) => do
  runTacq none seq

end Qq
