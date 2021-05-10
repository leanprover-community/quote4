import Lean
import Qq.ForLean.ReduceEval
import Qq.Reflect
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

structure UnquoteState where
  -- maps quoted expressions in the old context to level parameter names in the new context
  levelSubst : HashMap Expr Level := {}

  -- maps quoted expressions in the old context to expressions in the new context
  exprSubst : HashMap Expr Expr := {}

  -- new unquoted local context
  unquoted := LocalContext.empty

  -- maps free variables in the new context to expressions in the old context
  subst : HashMap Expr Expr := {}

  levelNames : List Name := []

abbrev UnquoteM := StateT UnquoteState MetaM

partial def unquoteLevel (e : Expr) : UnquoteM Level := do
  let e ← whnf e
  match (← get).levelSubst.find? e with
    | some l => return l
    | _ => ()
  let Expr.const c _ _ ← pure e.getAppFn | throwError "unquoteLevel: {e}"
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``Level.zero, 1 => levelZero
    | ``Level.succ, 2 => mkLevelSucc (← unquoteLevel (e.getArg! 0))
    | ``Level.max, 3 => mkLevelMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
    | ``Level.imax, 3 => mkLevelIMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
    | ``Level.param, 2 => mkLevelParam (← reduceEval (e.getArg! 0))
    | ``Level.mvar, 2 => mkLevelMVar (← reduceEval (e.getArg! 0))
    | _, _ => throwError "unquoteLevel: {e}"

partial def unquoteLevelList (e : Expr) : UnquoteM (List Level) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    []
  else if e.isAppOfArity ``List.cons 3 then
    (← unquoteLevel (e.getArg! 1)) :: (← unquoteLevelList (e.getArg! 2))
  else
    throwFailedToEval e

partial def unquoteExpr (e : Expr) : UnquoteM Expr := do
  if e.isAppOf ``reflect then return e.getArg! 2
  if e.isAppOf ``QQ.quoted && (e.getArg! 1).isFVar then return e.getArg! 1
  if e.isAppOf ``QQ.quoted && (e.getArg! 1).isMVar then
    match (← get).exprSubst.find? (e.getArg! 1) with
      | some e => return e
      | _ => ()
  let e ← whnf e
  let Expr.const c _ _ ← pure e.getAppFn | throwError "unquoteExpr {e}"
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``Expr.bvar, 2 => mkBVar (← reduceEval (e.getArg! 0))
    | ``Expr.fvar, 2 => mkFVar (← reduceEval (e.getArg! 0))
    | ``Expr.mvar, 2 => mkMVar (← reduceEval (e.getArg! 0))
    | ``Expr.sort, 2 => mkSort (← unquoteLevel (e.getArg! 0))
    | ``Expr.const, 3 => mkConst (← reduceEval (e.getArg! 0)) (← unquoteLevelList (e.getArg! 1))
    | ``Expr.app, 3 => mkApp (← unquoteExpr (e.getArg! 0)) (← unquoteExpr (e.getArg! 1))
    | ``Expr.lam, 4 =>
      mkLambda (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
    | ``Expr.forallE, 4 =>
      mkForall (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
    | ``Expr.letE, 5 =>
      mkLet (← reduceEval (e.getArg! 0)) (← unquoteExpr (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
        (← unquoteExpr (e.getArg! 3)) (← evalNonDepData (e.getArg! 4))
    | ``Expr.lit, 2 => mkLit (← reduceEval (e.getArg! 0))
    | ``Expr.proj, 4 =>
      mkProj (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
    | _, _ => throwError "unquoteExpr {e}"; throwFailedToEval e

def unquoteLCtx : UnquoteM Unit := do
  for ldecl in (← getLCtx) do
    let fv := ldecl.toExpr
    let ty := ldecl.type
    let whnfTy ← whnf ty
    if whnfTy.isAppOf ``QQ then
      let qTy := whnfTy.appArg!
      let newTy ← unquoteExpr qTy
      modify fun s => { s with
        unquoted := s.unquoted.addDecl $
          LocalDecl.cdecl ldecl.index ldecl.fvarId ldecl.userName newTy ldecl.binderInfo
        subst := s.subst.insert fv (mkApp2 (mkConst ``QQ.quoted) qTy fv)
        exprSubst := s.exprSubst.insert fv fv
      }
    else if whnfTy.isAppOf ``Level then
      modify fun s => { s with
        levelNames := ldecl.userName :: s.levelNames
        levelSubst := s.levelSubst.insert fv (mkLevelParam ldecl.userName)
      }
    else
      let Level.succ u _ ← getLevel ty | ()
      let LOption.some inst ← trySynthInstance (mkApp (mkConst ``Reflect [u]) ty) | ()
      modify fun s => { s with
        unquoted := s.unquoted.addDecl ldecl
        subst := s.subst.insert fv (mkApp3 (mkConst ``reflect [u]) ty inst fv)
        exprSubst := s.exprSubst.insert fv fv
      }

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
  | Expr.bvar i _ => mkApp (mkConst ``mkBVar) (reflect i)
  | e@(Expr.fvar i _) => do
    let some r ← s.find? e | throwError "unknown free variable {e}"
    r
  | e@(Expr.mvar i _) => throwError "resulting term contains metavariable {e}"
  | Expr.sort u _ => do mkApp (mkConst ``mkSort) (← quoteLevel u)
  | Expr.const n ls _ => do mkApp2 (mkConst ``mkConst) (reflect n) (← quoteLevelList ls)
  | Expr.app a b _ => do mkApp2 (mkConst ``mkApp) (← quoteExpr s a) (← quoteExpr s b)
  | Expr.lam n t b d => do
    mkApp4 (mkConst ``mkLambda) (reflect n) (reflect d.binderInfo) (← quoteExpr s t) (← quoteExpr s b)
  | Expr.forallE n t b d => do
    mkApp4 (mkConst ``mkForall) (reflect n) (reflect d.binderInfo) (← quoteExpr s t) (← quoteExpr s b)
  | Expr.letE n t v b d => do
    mkApp5 (mkConst ``mkLet) (reflect n) (← quoteExpr s t) (← quoteExpr s v) (← quoteExpr s b) (reflect d.nonDepLet)
  | Expr.lit l _ => mkApp (mkConst ``mkLit) (reflect l)
  | Expr.proj n i e _ => do mkApp3 (mkConst ``mkProj) (reflect n) (reflect i) (← quoteExpr s e)
  | e => throwError "quoteExpr todo {e}"

def unquoteMVars (mvars : Array MVarId) : UnquoteM (HashMap MVarId Expr × HashMap MVarId (MetaM Expr)) := do
  let mut exprMVarSubst : HashMap MVarId Expr := HashMap.empty
  let mut mvarSynth : HashMap MVarId (MetaM Expr) := {}

  unquoteLCtx

  let lctx ← getLCtx
  for mvar in mvars do
    let mdecl ← (← getMCtx).getDecl mvar
    if !(lctx.isSubPrefixOf mdecl.lctx && mdecl.lctx.isSubPrefixOf lctx) then
      throwError "incompatible metavariable {mvar}\n{MessageData.ofGoal mvar}"

    let newLCtx := (← get).unquoted
    let newLocalInsts ← determineLocalInstances newLCtx
    let subst := (← get).subst

    let ty ← whnf mdecl.type
    let ty ← instantiateMVars ty
    if ty.isAppOf ``QQ then
      let et := ty.getArg! 0
      let newET ← unquoteExpr et
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts newET
      modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar }
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.insert mvar do
        mkApp2 (mkConst ``QQ.qq) et (← quoteExpr subst (← instantiateMVars newMVar))
    else if ty.isSort then
      let u ← mkFreshLevelMVar
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts (mkSort u)
      modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar }
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.insert mvar do
        mkApp (mkConst ``QQ) (← quoteExpr subst (← instantiateMVars newMVar))
    else if ty.isAppOf ``Level then
      let newMVar ← mkFreshLevelMVar
      modify fun s => { s with levelSubst := s.levelSubst.insert (mkMVar mvar) newMVar }
      mvarSynth := mvarSynth.insert mvar do
        quoteLevel (← instantiateLevelMVars newMVar)
    else
      throwError "unsupported type {ty}"

  (exprMVarSubst, mvarSynth)

end Impl

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Impl

def Impl.macro (t : Syntax) (expectedType : Expr) : TermElabM Expr := do
  let lastId := (← mkFreshExprMVar expectedType).mvarId!
  let mvars := (← getMVars expectedType).push lastId
  let ((exprMVarSubst, mvarSynth), s) ← (unquoteMVars mvars).run {}

  let lastId := (exprMVarSubst.find! mvars.back).mvarId!
  let lastDecl ← Lean.Elab.Term.getMVarDecl lastId

  withLevelNames s.levelNames do
    resettingSynthInstanceCache do
      withLCtx lastDecl.lctx lastDecl.localInstances do
        let t ← Lean.Elab.Term.elabTerm t lastDecl.type
        let t ← ensureHasType lastDecl.type t
        synthesizeSyntheticMVars false
        if (← logUnassignedUsingErrorInfos (← getMVars t)) then
          throwAbortTerm
        assignExprMVar lastId t

    for newLevelName in (← getLevelNames) do
      if s.levelNames.contains newLevelName || (← isLevelFVar newLevelName).isSome then
        ()
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

  for mvar in mvars do
    let some synth ← mvarSynth.find? mvar | ()
    let mvar := mkMVar mvar
    let (true) ← isDefEq mvar (← synth) | throwError "cannot assign metavariable {mvar}"

  instantiateMVars (mkMVar mvars.back)

scoped elab (name := q) "q(" t:term ")" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then tryPostpone
  let expectedType ← whnf expectedType

  if expectedType.isMVar then
    -- support `#check q(foo)`
    let u ← mkFreshExprMVar (mkConst ``Level)
    let u' := mkApp (mkConst ``mkSort) u
    let t ← mkFreshExprMVar (mkApp (mkConst ``QQ) u')
    let (true) ← isDefEq expectedType (mkApp (mkConst ``QQ) (mkApp2 (mkConst ``QQ.quoted) u' t)) |
      throwError "expected type unknown"
  else if !expectedType.isAppOfArity ``QQ 1 then
    throwError "expected expected type Q(.), got {expectedType}"

  Impl.macro t expectedType

scoped elab (name := Q) "Q(" t:term ")" : term <= expectedType => do
  let u ← mkFreshLevelMVar
  let (true) ← isDefEq expectedType (mkSort u) |
    throwError "expected expected type Sort _, got {expectedType}"
  Impl.macro t expectedType

-- support `QQ (← foo) ∨ False`
macro_rules
  | `(Q($t)) => do
    let (lifts, t) ← Do.ToCodeBlock.expandLiftMethod t
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(Q($t))
    for lift in lifts do
      t ← `(let $(lift[2][0]):ident := $(lift[2][3][0]); $t)
    t
  | `(q($t)) => do
    let (lifts, t) ← Do.ToCodeBlock.expandLiftMethod t
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(q($t))
    for lift in lifts do
      t ← `(let $(lift[2][0]):ident := $(lift[2][3][0]); $t)
    t
