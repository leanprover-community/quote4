import Lean
import Qq.ForLean.ReduceEval
import Qq.ForLean.Abstract
import Qq.ForLean.TermElab
import Qq.Reflect
import Qq.Typ
import Qq.PostponedTactic

open Lean Meta Std Elab Term

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

def isLevelFVar (n : Name) : MetaM (Option Expr) := do
  match (← getLCtx).findFromUserName? n with
    | none => none
    | some decl =>
      if ← isDefEq decl.type (mkConst ``Level) then
        some decl.toExpr
      else
        none

syntax (name := postponedQuoteLevel) "postponedQuoteLevel" ident : term

def setUnquotedLevel (quotedMVar : Expr) (unquoted : Level) : MetaM Unit := do
  dbg_trace "setUnquotedLevel {quotedMVar.mvarId!} {unquoted}"
  assignLevelMVar (quotedMVar.mvarId!.mkStr "_qq_unquoted") unquoted

def getUnquotedLevel? (quotedMVar : Expr) : MetaM (Option Level) := do
  (← getMCtx).getLevelAssignment? (quotedMVar.mvarId!.mkStr "_qq_unquoted")

def mkLevelAbbrev (e : Level) : MetaM Syntax := do
  let id := (← mkFreshId).mkStr "_qq_abbr"
  assignLevelMVar id e
  mkCIdentRaw id

def getLevelAbbrev? (id : Syntax) : MetaM (Option Level) := do
  (← getMCtx).getLevelAssignment? id.getId

def getLevelAbbrev (id : Syntax) : MetaM Level := do
  match ← getLevelAbbrev? id with
    | some e => e
    | none => throwError "cannot retrieve abbreviation {id}"

def mkPostponedQuoteLevel (e : Level) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar (mkConst ``Level) MetavarKind.syntheticOpaque
  let stx ← `(postponedQuoteLevel $(← mkLevelAbbrev e))
  dbg_trace "mk {stx}"
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  setUnquotedLevel mvar e
  pure mvar

def quoteLevel : Level → TermElabM Expr
  | Level.zero _ => pure $ mkConst ``levelZero
  | Level.succ u _ => do mkApp (mkConst ``mkLevelSucc) (← quoteLevel u)
  | l@(Level.mvar n _) => mkPostponedQuoteLevel l
  | Level.max a b _ => do mkApp2 (mkConst ``mkLevelMax) (← quoteLevel a) (← quoteLevel b)
  | Level.imax a b _ => do mkApp2 (mkConst ``mkLevelIMax) (← quoteLevel a) (← quoteLevel b)
  | Level.param n _ => do
    match ← isLevelFVar n with
    | some fv => fv
    | none =>
      match ← getExprMVarAssignment? n with
      | some e => e
      | none =>
        throwError "universe parameter {n} does not exist in local context"

@[termElab «postponedQuoteLevel»]
def elabPostponedQuoteLevel : TermElab
  | stx@`(postponedQuoteLevel $id), _ => do
    tryPostpone
    let l ← instantiateLevelMVars (← mkLevelMVar id.getId)
    if l.isMVar then
      -- dbgPostponementState
      dbg_trace "cannot quote level metavariable {l}"
      throwError "cannot quote level metavariable {l}"
    quoteLevel l
  | _, _ => throwUnsupportedSyntax

def quoteLevelList : List Level → TermElabM Expr
  | [] => mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Level)
  | l::ls => do
    mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Level)
      (← quoteLevel l) (← quoteLevelList ls)

def mkAbbrev (e : Expr) : MetaM Syntax := do
  let id := (← mkFreshId).mkStr "_qq_abbr"
  assignExprMVar id e
  mkCIdentRaw id

def getAbbrev? (id : Syntax) : MetaM (Option Expr) :=
  getExprMVarAssignment? id.getId

def getAbbrev (id : Syntax) : MetaM Expr := do
  match ← getAbbrev? id with
    | some e => e
    | none => throwError "cannot retrieve abbreviation {id}"

syntax (name := postponedQuoteExpr) "postponedQuoteExpr" ident : term

def setUnquoted (quotedMVar : Expr) (unquoted : Expr) : MetaM Unit :=
  assignExprMVar (quotedMVar.mvarId!.mkStr "_qq_unquoted") unquoted

def getUnquoted? (quotedMVar : Expr) : MetaM (Option Expr) :=
  getExprMVarAssignment? (quotedMVar.mvarId!.mkStr "_qq_unquoted")

def mkPostponedQuoteExpr (e : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar (mkConst ``Expr) MetavarKind.syntheticOpaque
  let stx ← `(postponedQuoteExpr $(← mkAbbrev e))
  dbg_trace "mk {stx} {e}"
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  setUnquoted mvar e
  pure mvar

def setQuoted (unquotedMVar : Expr) (quoted : Expr) : MetaM Unit :=
  assignExprMVar (unquotedMVar.mvarId!.mkStr "_qq_quoted") quoted

def getQuoted? (unquotedMVar : Expr) : MetaM (Option Expr) :=
  getExprMVarAssignment? (unquotedMVar.mvarId!.mkStr "_qq_quoted")

private constant unquoteStuck (α : Sort u) (mvarId : Name) : α := sorryAx α

@[inline] constant betaRev' (e : Expr) (revArgs : List Expr) : Expr :=
  e.betaRev revArgs.toArray

partial def quoteExpr (e : Expr) : TermElabM Expr := do
  dbg_trace "quoteExpr {e}"
  match e with
  | e@(Expr.app (Expr.app (Expr.const ``unquoteStuck _ _) ty _) mvarId _) => do
    let mvarId ← reduceEval mvarId
    match ← getQuoted? (mkMVar mvarId) with
    | some q => q
    | _ => throwError "quoteExpr {e}"
  | Expr.bvar i _ => mkApp (mkConst ``mkBVar) (reflect i)
  | e@(Expr.fvar i _) => do
    let ty ← whnf (← inferType e)
    if ty.isAppOfArity ``QQ 1 then
      mkApp2 (mkConst ``QQ.quoted) (ty.getArg! 0) e
    else
      let Level.succ u _ ← getLevel ty | throwError "cannot determine level {e}"
      let inst ← synthInstance (mkApp (mkConst ``Reflect [u]) ty)
      mkApp3 (mkConst ``reflect [u]) ty inst e
  | e@(Expr.mvar i _) => do
    match ← getQuoted? e with
    | some q => q
    | _ => mkPostponedQuoteExpr e
  | e@(Expr.sort u _) => do
    mkApp (mkConst ``mkSort) (← quoteLevel u)
  | e@(Expr.const n ls _) => do
    assert! n != ``unquoteStuck
    mkApp2 (mkConst ``Lean.mkConst) (reflect n) (← quoteLevelList ls)
  | e@(Expr.app _ _ _) => do
    let fn ← quoteExpr e.getAppFn
    let args ← e.getAppArgs.mapM quoteExpr
    if e.getAppFn.isFVar then -- TODO make configurable
      mkApp2 (mkConst ``betaRev') fn $
        args.foldl (flip $ mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Expr))
          (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Expr))
    else
      pure $ args.foldl (mkApp2 (mkConst ``mkApp)) fn
  -- | e@(Expr.app a b _) => do
  --   mkApp2 (mkConst ``mkApp) (← quoteExpr a) (← quoteExpr b)
  | Expr.lam n t b d => do
    mkApp4 (mkConst ``mkLambda) (reflect n) (reflect d.binderInfo) (← quoteExpr t) (← quoteExpr b)
  | Expr.forallE n t b d => do
    mkApp4 (mkConst ``mkForall) (reflect n) (reflect d.binderInfo) (← quoteExpr t) (← quoteExpr b)
  | Expr.letE n t v b d => do
    mkApp5 (mkConst ``mkLet) (reflect n) (← quoteExpr t) (← quoteExpr v) (← quoteExpr b) (reflect d.nonDepLet)
  | Expr.lit l _ => mkApp (mkConst ``mkLit) (reflect l)
  | Expr.proj n i e _ => do mkApp3 (mkConst ``mkProj) (reflect n) (reflect i) (← quoteExpr e)
  | e@(Expr.mdata _ _ _) => throwError "quoteExpr todo {e}"

open Tactic in scoped elab "quoteExprAfterDefaults" id:ident : tactic => do
  let t ← instantiateMVars (← getAbbrev id)
  if t.hasMVar then
    let mvars ← getMVars t
    if ← logUnassignedUsingErrorInfos mvars then
      throwAbortTerm
    else if mvars.isEmpty then
      throwError "cannot quote expression, contains universe metavariables: {t}"
    else
      throwError "cannot quote expression, contains metavariable:\n{t}\n{← Meta.ppGoal mvars.back}"
  closeMainGoal (← quoteExpr t) (checkUnassigned := false)

@[termElab «postponedQuoteExpr»]
def elabPostponedQuoteExpr : TermElab
  | stx@`(postponedQuoteExpr $id), _ => do
      let t ← instantiateMVars (← getAbbrev id)
      tryPostpone
      if t.hasMVar then
        dbg_trace "by quoteExprAfterDefaults {id}"
        elabTerm (← `(by quoteExprAfterDefaults $id)) (mkConst ``Expr)
        -- if ← logUnassignedUsingErrorInfos (← getMVars t) then
        --   throwError ""
        --   -- throwAbortTerm
        -- else
        --   throwError "cannot quote expression, contains metavariables: {t}"
      else
        dbg_trace stx
        let res ← quoteExpr t
        dbg_trace "postponedQuoteExpr {t}\n-> {res}"
        -- dbgPostponementState
        res

  | _, _ => throwUnsupportedSyntax

abbrev UnquoteM := ReaderT MVarId <| ReaderT MetavarDecl TermElabM

def withQuotedLCtx (k : UnquoteM α) : UnquoteM α := do
  let decl ← readThe MetavarDecl
  withLCtx decl.lctx decl.localInstances k

partial def unquoteLevel (e : Expr) : UnquoteM Level := do
  let e ← whnf e
  if e.isAppOfArity ``Level.zero 1 then levelZero
  else if e.isAppOfArity ``Level.succ 2 then mkLevelSucc (← unquoteLevel (e.getArg! 0))
  else if e.isAppOfArity ``Level.max 3 then mkLevelMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.imax 3 then mkLevelIMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.param 2 then mkLevelParam (← reduceEval (e.getArg! 0))
  -- else if e.isAppOfArity ``Level.mvar 2 then mkLevelMVar (← reduceEval (e.getArg! 0))
  else if e.isFVar then mkLevelParam <|<- withQuotedLCtx do (← getFVarLocalDecl e).userName
  else if e.isMVar then
    match ← getUnquotedLevel? e with
      | some lvl => do
        dbg_trace "short circuit level {e} {lvl}"
        lvl
      | _ => throwError "cannot unquote level {e}"
  else
    let id ← mkFreshId
    assignExprMVar id e
    mkLevelParam id
    -- throwError "cannot unquote level {e}"
    -- let name ← mkAbstractedLevelName e
    -- let l := mkLevelParam name
    -- modify fun s => { s with
    --   levelSubst := s.levelSubst.insert e l
    --   levelBackSubst := s.levelBackSubst.insert l e
    -- }
    -- l

partial def unquoteLevelList (e : Expr) : UnquoteM (List Level) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    []
  else if e.isAppOfArity ``List.cons 3 then
    (← unquoteLevel (e.getArg! 1)) :: (← unquoteLevelList (e.getArg! 2))
  else
    throwError "cannot unquote level list {e}"

def mkAbstractedLevelName (e : Expr) : MetaM Name :=
  e.getAppFn.constName?.getD `udummy

def mkAbstractedName (e : Expr) : MetaM Name :=
  e.getAppFn.constName?.getD `dummy

syntax (name := postponedUnquoteExpr) "postponedUnquoteExpr" ident ident : term

def mkPostponedUnquoteExpr (quotedMVar : MVarId) (e : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprMVar none MetavarKind.syntheticOpaque
  let stx ← `(postponedUnquoteExpr $(mkCIdentRaw quotedMVar) $(← mkAbbrev e))
  dbg_trace "mk {stx}"
  registerSyntheticMVar stx mvar.mvarId! (SyntheticMVarKind.postponed (← saveContext))
  -- setUnquoted mvar e
  pure mvar

def mkStuckUnquoteMVar (e : Expr) (ty : Expr) : MetaM MVarId := do
  dbg_trace "\n\n\n\n"
  for (mvar, assg) in (← getMCtx).eAssignment.toList do
    match mvar with
      | Name.str mvar "_qq_quoted" _ =>
        try
          let (true) ← isDefEq assg e | ()
          dbg_trace "found {mvar}\n  {unQ assg}\n  {unQ e}"
          return mvar
        catch _ => ()
      | _ => ()
  let mvar ← mkFreshExprMVar ty MetavarKind.syntheticOpaque
  setQuoted mvar e
  -- let u ← getLevel ty
  -- let res ← mkApp2 (mkConst ``unquoteStuck [u]) ty e
  dbg_trace "unquote expr stuck proj {mvar} {ty}\n  {unQ e}\n{← Meta.ppGoal mvar.mvarId!}"
  mvar.mvarId!

  where unQ e := if e.isAppOf ``QQ.quoted then e.getArg! 1 else e

def mkStuckUnquoteExpr (e : Expr) (ty : Expr) : MetaM Expr := do
  mkApp2 (mkConst ``unquoteStuck [← getLevel ty]) ty
    (reflect (← mkStuckUnquoteMVar e ty))

partial def reduceUnquotedLCtx (e : Expr) (quoted unquoted : LocalContext) : LocalContext := do
  if unquoted.isEmpty then
    unquoted
  else
    match unquoted.lastDecl with -- wtf api
    | none => reduceUnquotedLCtx e quoted unquoted.pop
    | some decl =>
      if (quoted.find? decl.fvarId).isSome && (e.hasMVar || e.containsFVar decl.fvarId) then
        unquoted
      else
        reduceUnquotedLCtx e quoted unquoted.pop

mutual

partial def unquoteExprCore (e : Expr) : UnquoteM Expr := do
  dbg_trace "unquoteExprCore {e}"
  let e ← withQuotedLCtx do whnfHeadPred e fun hd => !hd.isAppOf ``reflect && !hd.isAppOf ``QQ.quoted
  if e.isAppOf ``reflect then return e.getArg! 2
  if e.isAppOfArity ``QQ.quoted 2 then
    let a ← withQuotedLCtx do whnf (e.getArg! 1)
    if a.isAppOfArity ``QQ.qq 2 then
      unquoteExprCore (a.getArg! 1)
    else if a.isFVar then
      a
    else
      let ty ← unquoteExpr (e.getArg! 0)
      -- dbg_trace e
      dbg_trace "\n\n\n\n\n{← withQuotedLCtx do
        Meta.ppGoal (← mkFreshExprMVar (← inferType e)).mvarId!}"
      withLCtx (reduceUnquotedLCtx e (← readThe MetavarDecl).lctx (← getLCtx)) {} do
        mkStuckUnquoteExpr e ty
  else do
  -- match e with
  --   | Expr.proj ``QQ 0 a _ => do
  --     dbg_trace "unquoteExprCore proj {e}"
  --     let a ← whnf a
  --     if a.isFVar then
  --       return a
  --     else
  --       let ta ← withQuotedLCtx do whnf (← inferType a)
  --       if !ta.isAppOfArity ``QQ 1 then throwError "unquoteExpr: {ta}"
  --       let ty ← unquoteExpr (ta.getArg! 0)
  --       let u ← getLevel ty
  --       let res ← mkApp2 (mkConst ``unquoteStuck [u]) ty e
  --       dbg_trace "unquote expr stuck proj {res}"
  --       return res
  --   | _ => ()
  let nargs := e.getAppNumArgs
  match e.getAppFn, nargs with
    | mvar@(Expr.mvar _ _), _ =>
      match ← getUnquoted? mvar with
        | some unquoted => unquoted
        | _ =>
          dbg_trace "unquote expr mvar {e}"
          throwError "unquoteExpr: {e}"
    | Expr.const c _ _, _ =>
      match c, nargs with
        | ``betaRev', 2 => betaRev' (← unquoteExpr (e.getArg! 0)) (← unquoteExprList (e.getArg! 1))
        | ``Expr.bvar, 2 => do
          let decls := (← getLCtx).decls
          let i ← reduceEval (e.getArg! 0)
          let some ldecl ← if decls.size == 0 then none else decls.get! (decls.size - i - 1)
            | throwError "cannot resolve bound variable #{i}\n{← Meta.ppGoal (← mkFreshExprMVar none).mvarId!}"
          ldecl.toExpr
        | ``Expr.sort, 2 => mkSort (← unquoteLevel (e.getArg! 0))
        | ``Expr.const, 3 => Lean.mkConst (← reduceEval (e.getArg! 0)) (← unquoteLevelList (e.getArg! 1))
        | ``Expr.app, 3 => mkApp (← unquoteExpr (e.getArg! 0)) (← unquoteExpr (e.getArg! 1))
        | ``Expr.lam, 4 =>
          withLocalDecl (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
              (← unquoteExpr (e.getArg! 1)) fun x => do
            dbg_trace "mkLambdaFVars"
            mkLambdaFVars #[x] (← unquoteExpr (e.getArg! 2))
        | ``Expr.forallE, 4 =>
          withLocalDecl (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
              (← unquoteExpr (e.getArg! 1)) fun x => do
            let b ← unquoteExpr (e.getArg! 2)
            dbg_trace "mkForallFVars before {(← getMCtx).dAssignment.size}"
            let r  ← mkForallFVars #[x] b
            dbg_trace "mkForallFVars after {(← getMCtx).dAssignment.size}"
            r
        | ``Expr.letE, 5 =>
          withLetDecl (← reduceEval (e.getArg! 0)) (← unquoteExpr (e.getArg! 1))
              (← unquoteExpr (e.getArg! 2)) fun x => do
            dbg_trace "mkLetFVars"
            -- what is nondepdata?
            mkLetFVars #[x] (← unquoteExpr (e.getArg! 3)) false
        | ``Expr.lit, 2 => mkLit (← reduceEval (e.getArg! 0))
        | ``Expr.proj, 4 =>
          mkProj (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
        | _, _ =>
          dbg_trace "unquote stuck {e}"
          throwError "unquoteExpr: {e}"
    | _, _ =>
      dbg_trace "unquote stuck 2 {e}"
      throwError "unquoteExpr: {e}"

partial def unquoteExpr (e : Expr) : UnquoteM Expr := do
  try unquoteExprCore e
  catch ex =>
    dbg_trace "ERRORERRORERRORERROR"
    dbg_trace (e,← ex.toMessageData.toString)
    mkPostponedUnquoteExpr (← readThe MVarId) e

partial def unquoteExprList (e : Expr) : UnquoteM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    []
  else if e.isAppOfArity ``List.cons 3 then
    (← unquoteExprCore (e.getArg! 1)) :: (← unquoteExprList (e.getArg! 2))
  else
    throwError "cannot unquote expression list {e}"

end

@[termElab «postponedUnquoteExpr»]
def elabPostponedUnquoteExpr : TermElab
  | stx@`(postponedUnquoteExpr $quotedMVarId $id), _ => do
    let t ← instantiateMVars (← getAbbrev id)
    if t.getAppFn.isMVar then
      tryPostpone
    -- dbg_trace "{stx} -> {t}"
    let quotedMVarId := quotedMVarId.getId
    unquoteExprCore t quotedMVarId (← Meta.getMVarDecl quotedMVarId)

  | _, _ => throwUnsupportedSyntax

def determineLocalInstances (lctx : LocalContext) : MetaM LocalInstances := do
  let mut localInsts : LocalInstances := {}
  for ldecl in lctx do
    match (← isClass? ldecl.type) with
      | some c => localInsts := localInsts.push { className := c, fvar := ldecl.toExpr }
      | none => ()
  localInsts

def setupUnassgMVars (e : Expr) : UnquoteM Unit := do
  -- dbg_trace "setupUnassgMVars {e}"
  for mvarId in ← getMVars (← instantiateMVars e) do
    let mvar ← mkMVar mvarId
    if ← Meta.isExprMVarAssigned mvarId then continue
    if (← getUnquoted? mvar).isSome then continue
    if (← getUnquotedLevel? mvar).isSome then continue
    dbg_trace "setupUnassgMVars found mvar {mvar}"
    withMVarContext mvarId do
      -- dbg_trace ← Meta.ppGoal mvarId
      let ty ← whnf (← inferType mvar)
      -- dbg_trace ty
      if ty.isAppOfArity ``Level 0 then
        dbg_trace "assigning {mvarId} of type level"
        assignExprMVar mvarId (← mkPostponedQuoteLevel (← mkFreshLevelMVar))
      if ty.isAppOfArity ``QQ 1 then
        -- dbg_trace "assigning {mvarId}"
        assignExprMVar mvarId <|
          mkApp2 (mkConst ``QQ.qq) (ty.getArg! 0) <|<-
          mkPostponedQuoteExpr (← mkFreshExprMVar (← unquoteExpr (ty.getArg! 0) (← read)))
      -- dbg_trace "done"

def UnquoteM.run' (unquoted : LocalContext) (qId : MVarId) (qDecl : MetavarDecl) (k : UnquoteM α) : TermElabM α := do
  withLCtx unquoted (← determineLocalInstances unquoted) do k qId qDecl

def unquotingLCtx (k : UnquoteM α) : TermElabM α := do
  let qId := (← mkFreshExprMVar (mkSort levelZero)).mvarId!
  let qDecl ← Meta.getMVarDecl qId
  let mut unquoted : LocalContext := {}
  let mut levelNames := #[]

  for ldecl in ← getLCtx do
    let fv := ldecl.toExpr
    let ty := ldecl.type
    let whnfTy ← whnf ty

    if whnfTy.isAppOf ``QQ then
      let qTy := whnfTy.appArg!
      let newTy ← UnquoteM.run' unquoted qId qDecl do
        setupUnassgMVars qTy
        unquoteExpr qTy
      unquoted := unquoted.addDecl $
        LocalDecl.cdecl ldecl.index ldecl.fvarId ldecl.userName newTy ldecl.binderInfo

    else if whnfTy.isAppOf ``Level then
      unquoted := unquoted.addDecl ldecl
      levelNames := levelNames.push ldecl.userName

    else
      let Level.succ u _ ← getLevel ty | ()
      let LOption.some inst ← trySynthInstance (mkApp (mkConst ``Reflect [u]) ty) | ()
      unquoted := unquoted.addDecl ldecl
      -- oldVars := oldVars.push fv
      -- let newFVarId := ldecl.fvarId.mkNum 1
      -- oldVars := oldVars.push fv
      -- newVars := newVars.push (mkFVar newFVarId)
      -- subst := subst.push <| mkApp3 (mkConst ``reflect [u]) ty inst fv
      -- parsed := parsed.push (← mkPostponedQuoteExpr ty, newFVarId)
      -- unwrapped := unwrapped.addDecl $
      --   LocalDecl.cdecl ldecl.index newFVarId ldecl.userName (mkConst ``Expr) ldecl.binderInfo

  withLevelNames levelNames.toList do
    let res ← resettingSynthInstanceCache do
      UnquoteM.run' unquoted qId qDecl k

    for newLevelName in ← getLevelNames do
      if levelNames.contains newLevelName || (← isLevelFVar newLevelName).isSome then
        ()
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

    res

end Impl

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Impl

scoped elab "q(" t:term ")" : term <= expectedType => do
  tryPostponeIfMVar expectedType
  let expectedType ← instantiateMVars (← whnf expectedType)
  -- dbg_trace "\n\n\n"
  let quotedET ←
    if expectedType.isAppOfArity ``QQ 1 then
      expectedType.getArg! 0
    else
      mkPostponedQuoteExpr (← unquotingLCtx mkFreshTypeMVar)
      -- mkFreshExprMVar (mkConst ``Expr)
  -- dbg_trace (expectedType, quotedET)
  dbg_trace "q({t}):"; dbg_trace ← Meta.ppGoal (← mkFreshExprMVar expectedType).mvarId!
  let res ← mkApp2 (mkConst ``QQ.qq) quotedET <|<- mkPostponedQuoteExpr <|<-
    unquotingLCtx do
      -- dbg_trace quotedET
      setupUnassgMVars quotedET
      let unquotedET ← unquoteExpr quotedET
      dbg_trace "unquotedET {unquotedET}"
      withPostponedTactics do
      Term.elabTermEnsuringType t unquotedET
  let res ← instantiateMVars res
  -- dbg_trace "q({t}) <= {expectedType} -> {res}"
  -- dbg_trace (← getLCtx).decls.toList.map fun x => (x.getD arbitrary).fvarId
  -- dbg_trace (← getMCtx).isWellFormed (← getLCtx) res
  -- dbgPostponementState
  res
  -- let (fvars, subst, unquoted) ← unquotingLCtx do
  --   withPostponedTactics do elabTerm t (← unquoteExpr quotedET)
  -- mkApp2 (mkConst ``QQ.qq) quotedET (← replaceFVars (← mkPostponedQuoteExpr unquoted) fvars subst)
  --  <| ← unquotingLCtx fun fvars subst => do
  --   let ← withPostponedTactics do elabTerm t (← unquoteExpr quotedET)

scoped elab "Q(" t:term ")" : term => do
  -- dbg_trace "\n\n\n"
  dbg_trace "Q({t}):"; dbg_trace ← Meta.ppGoal (← mkFreshExprMVar (mkSort levelZero)).mvarId!
  let res ← mkApp (mkConst ``QQ) <|<- mkPostponedQuoteExpr <|<-
    unquotingLCtx do
      withPostponedTactics do
      Term.elabTermEnsuringType t (mkSort (← mkFreshLevelMVar))
  let res ← instantiateMVars res
  -- dbg_trace "Q({t}) -> {res}"
  -- dbgPostponementState
  res

/-
support `Q(%(foo) ∨ False)`
-/

scoped syntax "%(" term ")" : term
scoped syntax "Type" "%(" term ")" : term
scoped syntax "Sort" "%(" term ")" : term

private partial def expandLiftMethod : Syntax → StateT (Array $ Syntax × Syntax × Syntax) MacroM Syntax
  | stx@`(Q($x)) => stx
  | stx@`(q($x)) => stx
  | `(%($term)) =>
    withFreshMacroScope do
      push (← `(a)) (← `(QQ _)) (← expandLiftMethod term)
      `(a)
  | `(Type %($term)) =>
    withFreshMacroScope do
      push (← `(u)) (← `(Level)) (← expandLiftMethod term)
      `(Type u)
  | `(Sort %($term)) =>
    withFreshMacroScope do
      push (← `(u)) (← `(Level)) (← expandLiftMethod term)
      `(Sort u)
  | stx => match stx with
    | Syntax.node k args => do Syntax.node k (← args.mapM expandLiftMethod)
    | stx => stx

  where
    push i t l : StateT (Array $ Syntax × Syntax × Syntax) MacroM Unit :=
      modify fun s => s.push (i, t, l)

macro_rules
  | `(Q($t)) => do
    let (t, lifts) ← expandLiftMethod t #[]
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(Q($t))
    for (a, ty, lift) in lifts do
      t ← `(let $a:ident : $ty := $lift; $t)
    t
  | `(q($t)) => do
    let (t, lifts) ← expandLiftMethod t #[]
    if lifts.isEmpty then Macro.throwUnsupported
    let mut t ← `(q($t))
    for (a, ty, lift) in lifts do
      t ← `(let $a:ident : $ty := $lift; $t)
    t

def or1 : List Q(Prop) → Q(Prop)
  | [] => q(False)
  | [p] => q(p)
  | p::ps => q(p ∨ %(or1 ps))

def or2 : List Q(Prop) → Q(Prop)
  | [] => q(False)
  | p::ps => q(p ∨ %(or2 ps))

theorem Or.elim {r : Prop} (h : p ∨ q) (hp : p → r) (hq : q → r) : r := by
  cases h
  case inl h => exact hp h
  case inr h => exact hq h

def orChange : (ps : List Q(Prop)) → Q(%(or1 ps) → %(or2 ps))
  | [] => q(id)
  | [p] => q(Or.inl)
  | p::(ps1::ps2) =>
    let ih := orChange (ps1 :: ps2)
    by exact
    q(by intro h
         cases h
         case inl h => exact Or.inl h
         case inr h => exact Or.inr (ih h)
         )
