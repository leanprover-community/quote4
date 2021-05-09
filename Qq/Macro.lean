import Lean
import Qq.ForLean.ReduceEval
import Qq.ForLean.ToExpr
import Qq.Typ
open Lean Meta Std

namespace Qq

namespace Impl

def evalBinderInfoData (e : Expr) : MetaM BinderInfo :=
  if e.isAppOfArity ``Expr.mkDataForBinder 7 then
    reduceEval (e.getArg! 6)
  else
    throwFailedToEval e

def evalNonDepData (e : Expr) : MetaM Bool :=
  if e.isAppOfArity ``Expr.mkDataForLet 7 then
    reduceEval (e.getArg! 6)
  else
    throwFailedToEval e

partial def evalLevel (levelSubst : HashMap MVarId Level) (e : Expr) : MetaM Level := do
  let e ← whnf e
  if e.isFVar then return mkLevelParam (← getFVarLocalDecl e).userName
  if e.isMVar then
    match levelSubst.find? e.mvarId! with
      | some l => return l
      | _=> ()
  let Expr.const c _ _ ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``Level.zero, 1 => levelZero
    | ``Level.succ, 2 => mkLevelSucc (← evalLevel levelSubst (e.getArg! 0))
    | ``Level.max, 3 => mkLevelMax (← evalLevel levelSubst (e.getArg! 0)) (← evalLevel levelSubst (e.getArg! 1))
    | ``Level.imax, 3 => mkLevelIMax (← evalLevel levelSubst (e.getArg! 0)) (← evalLevel levelSubst (e.getArg! 1))
    | ``Level.param, 2 => mkLevelParam (← reduceEval (e.getArg! 0))
    | ``Level.mvar, 2 => mkLevelMVar (← reduceEval (e.getArg! 0))
    | _, _ => throwFailedToEval e

partial def evalExpr (exprSubst : HashMap MVarId Expr) (levelSubst : HashMap MVarId Level) (e : Expr) : MetaM Expr := do
  if e.isAppOf ``toExpr then return e.getArg! 2
  if e.isAppOf ``QQ.quoted && (e.getArg! 1).isFVar then return e.getArg! 1
  if e.isAppOf ``QQ.quoted && (e.getArg! 1).isMVar then
    match exprSubst.find? (e.getArg! 1).mvarId! with
      | some e => return e
      | _ => ()
  let e ← whnf e
  let Expr.const c _ _ ← pure e.getAppFn | throwFailedToEval e
  let nargs := e.getAppNumArgs
  let _ : ReduceEval Level := ⟨evalLevel levelSubst⟩
  match c, nargs with
    | ``Expr.bvar, 2 => mkBVar (← reduceEval (e.getArg! 0))
    | ``Expr.fvar, 2 => mkFVar (← reduceEval (e.getArg! 0))
    | ``Expr.mvar, 2 => mkMVar (← reduceEval (e.getArg! 0))
    | ``Expr.sort, 2 => mkSort (← reduceEval (e.getArg! 0))
    | ``Expr.const, 3 => mkConst (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1))
    | ``Expr.app, 3 => mkApp (← evalExpr exprSubst levelSubst (e.getArg! 0)) (← evalExpr exprSubst levelSubst (e.getArg! 1))
    | ``Expr.lam, 4 =>
      mkLambda (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← evalExpr exprSubst levelSubst (e.getArg! 1))
        (← evalExpr exprSubst levelSubst (e.getArg! 2))
    | ``Expr.forallE, 4 =>
      mkForall (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← evalExpr exprSubst levelSubst (e.getArg! 1))
        (← evalExpr exprSubst levelSubst (e.getArg! 2))
    | ``Expr.letE, 5 =>
      mkLet (← reduceEval (e.getArg! 0))
        (← evalExpr exprSubst levelSubst (e.getArg! 1))
        (← evalExpr exprSubst levelSubst (e.getArg! 2))
        (← evalExpr exprSubst levelSubst (e.getArg! 3))
        (← evalNonDepData (e.getArg! 4))
    | ``Expr.lit, 2 => mkLit (← reduceEval (e.getArg! 0))
    | ``Expr.proj, 4 =>
      mkProj (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1))
        (← evalExpr exprSubst levelSubst (e.getArg! 2))
    | _, _ => throwFailedToEval e

def unquoteLCtx (lctx : LocalContext) : MetaM (LocalContext × HashMap Expr Expr × List Name) := do
  let mut unquoted := LocalContext.empty
  let mut subst := HashMap.empty
  let mut levelNames := []
  let exprMVarSubst := HashMap.empty
  let levelMVarSubst := HashMap.empty
  for ldecl in lctx do
    let fv := ldecl.toExpr
    let ty := ldecl.type
    let whnfTy ← whnf ty
    if whnfTy.isAppOf ``QQ then
      let qTy := whnfTy.appArg!
      let newTy ← evalExpr exprMVarSubst levelMVarSubst qTy
      unquoted := unquoted.addDecl $
        LocalDecl.cdecl ldecl.index ldecl.fvarId ldecl.userName newTy ldecl.binderInfo
      subst := subst.insert fv (mkApp2 (mkConst ``QQ.quoted) qTy fv)
    else if whnfTy.isAppOf ``Level then
      levelNames := ldecl.userName :: levelNames
    else do
      let Level.succ u _ ← getLevel ty | ()
      let LOption.some inst ← trySynthInstance (mkApp (mkConst ``ToExpr [u]) ty) | ()
      unquoted := unquoted.addDecl ldecl
      subst := subst.insert fv (mkApp3 (mkConst ``toExpr [u]) ty inst fv)
  (unquoted, subst, levelNames)

def determineLocalInstances (lctx : LocalContext) : MetaM LocalInstances := do
  let mut localInsts : LocalInstances := {}
  for ldecl in lctx do
    match (← isClass? ldecl.type) with
      | some c => localInsts := localInsts.push { className := c, fvar := ldecl.toExpr }
      | none => ()
  localInsts

def isLevelFVar (n : Name) : MetaM (Option Expr) := do
  match (← getLCtx).findFromUserName? n with
    | none => none
    | some decl =>
      if ← isDefEq decl.type (mkConst ``Level) then
        some decl.toExpr
      else
        none

def quoteLevel : Level → MetaM Expr
  | Level.zero _ => mkConst ``levelZero
  | Level.succ u _ => do mkApp (mkConst ``mkLevelSucc) (← quoteLevel u)
  | Level.mvar n _ => throwError "level mvars not supported"
  | Level.max a b _ => do mkApp2 (mkConst ``mkLevelMax) (← quoteLevel a) (← quoteLevel b)
  | Level.imax a b _ => do mkApp2 (mkConst ``mkLevelIMax) (← quoteLevel a) (← quoteLevel b)
  | Level.param n _ => do
    let (some fv) ← isLevelFVar n | throwError "universe parameter {n} not of type Level"
    pure fv

def quoteLevelList : List Level → MetaM Expr
  | [] => mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Level)
  | l::ls => do
    mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Level)
      (← quoteLevel l) (← quoteLevelList ls)

def quoteExpr (s : HashMap Expr Expr) : Expr → MetaM Expr
  | Expr.bvar i _ => mkApp (mkConst ``mkBVar) (toExpr i)
  | e@(Expr.fvar i _) => (s.find? e).getD $
    mkApp (mkConst ``mkFVar) (toExpr i)
  | Expr.mvar i _ => throwError "mvars not supported"
  | Expr.sort u _ => do mkApp (mkConst ``mkSort) (← quoteLevel u)
  | Expr.const n ls _ => do mkApp2 (mkConst ``mkConst) (toExpr n) (← quoteLevelList ls)
  | Expr.app a b _ => do mkApp2 (mkConst ``mkApp) (← quoteExpr s a) (← quoteExpr s b)
  | Expr.lam n t b d => do
    mkApp4 (mkConst ``mkLambda) (toExpr n) (toExpr d.binderInfo) (← quoteExpr s t) (← quoteExpr s b)
  | Expr.forallE n t b d => do
    mkApp4 (mkConst ``mkForall) (toExpr n) (toExpr d.binderInfo) (← quoteExpr s t) (← quoteExpr s b)
  | Expr.letE n t v b d => do
    mkApp5 (mkConst ``mkLet) (toExpr n) (← quoteExpr s t) (← quoteExpr s v) (← quoteExpr s b) (toExpr d.nonDepLet)
  | Expr.lit l _ => mkApp (mkConst ``mkLit) (toExpr l)
  | Expr.proj n i e _ => do mkApp3 (mkConst ``mkProj) (toExpr n) (toExpr i) (← quoteExpr s e)
  | e => throwError "quoteExpr todo {e}"

end Impl

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Impl

def Impl.macro (t : Syntax) (expectedType : Expr) (capitalized : Bool) : TermElabM Expr := do

  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then tryPostpone

  -- support `#check q(foo)`
  if expectedType.isMVar then
    let u ← mkFreshExprMVar (mkConst ``Level)
    let u' := mkApp (mkConst ``mkSort) u
    let t ← mkFreshExprMVar (mkApp (mkConst ``QQ) u')
    let (true) ← isDefEq expectedType (mkApp (mkConst ``QQ) (mkApp2 (mkConst ``QQ.quoted) u' t)) |
      throwError "expected type unknown"

  let lctx ← getLCtx

  let (newLCtx, subst, levelNames) ← unquoteLCtx lctx
  let newLocalInsts ← determineLocalInstances newLCtx

  let lastId := (← mkFreshExprMVar expectedType).mvarId!
  let mvars := (← getMVars expectedType).push lastId
  let mut mvarSynth : Array (MetaM Expr) := #[]
  let mut exprMVarSubst : HashMap MVarId Expr := HashMap.empty
  let mut levelMVarSubst : HashMap MVarId Level := HashMap.empty

  for mvar in mvars do
    let mdecl ← Lean.Elab.Term.getMVarDecl mvar
    if !(lctx.isSubPrefixOf mdecl.lctx && mdecl.lctx.isSubPrefixOf lctx) then
      throwError "incompatible metavariable {mvar}\n{MessageData.ofGoal mvar}"

    let ty ← whnf mdecl.type
    let ty ← instantiateMVars ty
    if ty.isAppOf ``QQ && (!capitalized || mvar != lastId) then
      let et := ty.getArg! 0
      let newET ← evalExpr exprMVarSubst levelMVarSubst et
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts newET
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.push do
        mkApp2 (mkConst ``QQ.qq) et (← quoteExpr subst (← instantiateMVars newMVar))
    else if ty.isSort && mvar == lastId && capitalized then
      let u ← mkFreshLevelMVar
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts (mkSort u)
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.push do
        mkApp (mkConst ``QQ) (← quoteExpr subst (← instantiateMVars newMVar))
    else if ty.isAppOf ``Level && mvar != lastId then
      let newMVar ← mkFreshLevelMVar
      levelMVarSubst := levelMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.push do
        quoteLevel (← instantiateLevelMVars newMVar)
    else
      throwError "unsupported expected type {ty}"

  -- for (_, m) in exprMVarSubst.toArray do
  --   logInfo $ MessageData.ofGoal m.mvarId!

  let lastId := (exprMVarSubst.find! mvars.back).mvarId!
  let lastDecl ← Lean.Elab.Term.getMVarDecl lastId

  withLevelNames levelNames do
    resettingSynthInstanceCache do
      withLCtx lastDecl.lctx lastDecl.localInstances do
        -- logInfo lastDecl.type
        let t ← Lean.Elab.Term.elabTerm t lastDecl.type
        let t ← ensureHasType lastDecl.type t
        synthesizeSyntheticMVars false
        if (← logUnassignedUsingErrorInfos (← getMVars t)) then
          throwAbortTerm
        assignExprMVar lastId t

    for newLevelName in (← getLevelNames) do
      if levelNames.contains newLevelName || (← isLevelFVar newLevelName).isSome then
        ()
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

  for mvar in mvars, synth in mvarSynth do
    let mvar := mkMVar mvar
    let (true) ← isDefEq mvar (← synth) | throwError "cannot assign metavariable {mvar}"

  -- logInfo $ toString (← instantiateMVars (mkMVar mvars.back))
  instantiateMVars (mkMVar mvars.back)

scoped elab "q(" t:term ")" : term <= expectedType =>
  Impl.macro t expectedType (capitalized := false)

scoped elab "Q(" t:term ")" : term <= expectedType =>
  Impl.macro t expectedType (capitalized := true)

-- support `QQ (← foo) ∨ False`
macro_rules
  | `(Q($t)) => do
    let (lifts, t) ← Do.ToCodeBlock.expandLiftMethod t
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(Q($t))
    for lift in lifts do
      t ← `(have $(lift[2][0]):ident := $(lift[2][3][0]); $t)
    t
  | `(q($t)) => do
    let (lifts, t) ← Do.ToCodeBlock.expandLiftMethod t
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(q($t))
    for lift in lifts do
      t ← `(have $(lift[2][0]):ident := $(lift[2][3][0]); $t)
    t
