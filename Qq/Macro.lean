import Lean
import Qq.ForLean.ReduceEval
import Qq.ForLean.ToExpr
import Qq.Typ
open Lean Meta Std

namespace Qq

namespace Impl

def evalBinderInfoData (e : Expr) : MetaM BinderInfo :=
  if e.isAppOfArity ``Expr.mkDataForBinder 8 then
    reduceEval (e.getArg! 7)
  else
    throwFailedToEval e

def evalNonDepData (e : Expr) : MetaM Bool :=
  if e.isAppOfArity ``Expr.mkDataForLet 8 then
    reduceEval (e.getArg! 7)
  else
    throwFailedToEval e

structure UnquoteState where
  -- maps quoted expressions (of type Level) in the old context to level parameter names in the new context
  levelSubst : HashMap Expr Level := {}

  -- maps quoted expressions (of type Expr) in the old context to expressions in the new context
  exprSubst : HashMap Expr Expr := {}

  -- new unquoted local context
  unquoted := LocalContext.empty

  -- maps free variables in the new context to expressions in the old context (of type Expr)
  exprBackSubst : HashMap Expr Expr := {}

  -- maps free variables in the new context to levels in the old context (of type Level)
  levelBackSubst : HashMap Level Expr := {}

  levelNames : List Name := []

abbrev UnquoteM := StateT UnquoteState MetaM

open Name in
def addDollar : Name → Name
  | anonymous => mkStr anonymous "$"
  | str anonymous s _ => mkStr anonymous ("$" ++ s)
  | str n s _ => mkStr (addDollar n) s
  | num n i _ => mkNum (addDollar n) i

open Name in
def removeDollar : Name → Option Name
  | anonymous => none
  | str anonymous "$" _ => some anonymous
  | str anonymous s _ =>
    if s.startsWith "$" then mkStr anonymous (s.drop 1) else none
  | str n s _ => (removeDollar n).map (mkStr . s)
  | num n i _ => (removeDollar n).map (mkNum . i)

open Name in
def stripDollars : Name → Name
  | anonymous => anonymous
  | str n "$" _ => stripDollars n
  | str anonymous s _ =>
    let s := s.dropWhile (· = '$')
    if s = "" then anonymous else mkStr anonymous s
  | str n s _ => mkStr (stripDollars n) s
  | num n i _ => mkNum (stripDollars n) i

def addSyntaxDollar : Syntax → Syntax
  | Syntax.ident info rawVal            val  preresolved =>
    Syntax.ident info rawVal (addDollar val) preresolved
  | stx => panic! "addSyntaxDollar {stx}"

def mkAbstractedLevelName (e : Expr) : MetaM Name :=
  return e.getAppFn.constName?.getD `udummy ++ (← mkFreshId)

def isBad (e : Expr) : Bool := Id.run do
  if let Expr.const (Name.str _ "rec" _) _ _ := e.getAppFn then
    return true
  return false

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/How.20to.20WHNF.20without.20exposing.20recursors.3F/near/249743042
partial def whnf (e : Expr) (e0 : Expr := e) : MetaM Expr := do
  let e ← whnfCore e
  let e0 := if isBad e then e0 else e
  match ← unfoldDefinition? e with
    | some e => whnf e (if isBad e then e0 else e)
    | none => pure e0

partial def unquoteLevel (e : Expr) : UnquoteM Level := do
  let e ← whnf e
  if let some l := (← get).levelSubst.find? e then
    return l
  if e.isAppOfArity ``Level.zero 1 then pure levelZero
  else if e.isAppOfArity ``Level.succ 2 then return mkLevelSucc (← unquoteLevel (e.getArg! 0))
  else if e.isAppOfArity ``Level.max 3 then return mkLevelMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.imax 3 then return mkLevelIMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.param 2 then return mkLevelParam (← reduceEval (e.getArg! 0))
  else if e.isAppOfArity ``Level.mvar 2 then return mkLevelMVar (← reduceEval (e.getArg! 0))
  else
    let name ← mkAbstractedLevelName e
    let l := mkLevelParam name
    modify fun s => { s with
      levelSubst := s.levelSubst.insert e l
      levelBackSubst := s.levelBackSubst.insert l e
    }
    pure l

partial def unquoteLevelList (e : Expr) : UnquoteM (List Level) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    pure []
  else if e.isAppOfArity ``List.cons 3 then
    return (← unquoteLevel (e.getArg! 1)) :: (← unquoteLevelList (e.getArg! 2))
  else
    throwFailedToEval e

def mkAbstractedName (e : Expr) : MetaM Name :=
  return e.getAppFn.constName?.getD `dummy

@[inline] constant betaRev' (e : Expr) (revArgs : List Expr) : Expr :=
  e.betaRev revArgs.toArray

mutual
partial def unquoteExprList (e : Expr) : UnquoteM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    pure []
  else if e.isAppOfArity ``List.cons 3 then
    return (← unquoteExpr (e.getArg! 1)) :: (← unquoteExprList (e.getArg! 2))
  else
    throwFailedToEval e

partial def unquoteExpr (e : Expr) : UnquoteM Expr := do
  if e.isAppOfArity ``QQ.qq 2 then return ← unquoteExpr (e.getArg! 1)
  if e.isAppOfArity ``toExpr 3 then return e.getArg! 2
  let e ← whnf (← instantiateMVars e)
  let eTy ← withReducible <| whnf (← inferType e)
  if eTy.isAppOfArity ``QQ 1 then
    if let some e' := (← get).exprSubst.find? e then
      return e'
    let ty ← unquoteExpr (eTy.getArg! 0)
    let fvarId := FVarId.mk (← mkFreshId)
    let name ← mkAbstractedName e
    let fv := mkFVar fvarId
    modify fun s => { s with
      unquoted := s.unquoted.mkLocalDecl fvarId name ty
      exprSubst := s.exprSubst.insert e fv
      exprBackSubst := s.exprBackSubst.insert fv e
    }
    return fv
  let e ← whnf e
  let Expr.const c _ _ ← pure e.getAppFn | throwError "unquoteExpr: {e} : {eTy}"
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``betaRev', 2 => return betaRev' (← unquoteExpr (e.getArg! 0)) (← unquoteExprList (e.getArg! 1))
    | ``Expr.bvar, 2 => return mkBVar (← reduceEval (e.getArg! 0))
    /- | ``Expr.fvar, 2 => mkFVar (← reduceEval (e.getArg! 0)) -/
    /- | ``Expr.mvar, 2 => mkMVar (← reduceEval (e.getArg! 0)) -/
    | ``Expr.sort, 2 => return mkSort (← unquoteLevel (e.getArg! 0))
    | ``Expr.const, 3 => return mkConst (← reduceEval (e.getArg! 0)) (← unquoteLevelList (e.getArg! 1))
    | ``Expr.app, 3 => return mkApp (← unquoteExpr (e.getArg! 0)) (← unquoteExpr (e.getArg! 1))
    | ``Expr.lam, 4 =>
      return mkLambda (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
    | ``Expr.forallE, 4 =>
      return mkForall (← reduceEval (e.getArg! 0)) (← evalBinderInfoData (e.getArg! 3))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
    | ``Expr.letE, 5 =>
      return mkLet (← reduceEval (e.getArg! 0)) (← unquoteExpr (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
        (← unquoteExpr (e.getArg! 3)) (← evalNonDepData (e.getArg! 4))
    | ``Expr.lit, 2 => return mkLit (← reduceEval (e.getArg! 0))
    | ``Expr.proj, 4 =>
      return mkProj (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
    | _, _ => throwError "unquoteExpr: {e} : {eTy}"

end

def unquoteLCtx : UnquoteM Unit := do
  for ldecl in (← getLCtx) do
    let fv := ldecl.toExpr
    let ty := ldecl.type
    let whnfTy ← withReducible <| whnf ty
    if whnfTy.isAppOfArity ``QQ 1 then
      let qTy := whnfTy.appArg!
      let newTy ← unquoteExpr qTy
      modify fun s => { s with
        unquoted := s.unquoted.addDecl $
          LocalDecl.cdecl ldecl.index ldecl.fvarId (addDollar ldecl.userName) newTy ldecl.binderInfo
        exprBackSubst := s.exprBackSubst.insert fv fv
        exprSubst := s.exprSubst.insert fv fv
      }
    else if whnfTy.isAppOfArity ``Level 0 then
      modify fun s => { s with
        levelNames := ldecl.userName :: s.levelNames
        levelSubst := s.levelSubst.insert fv (mkLevelParam ldecl.userName)
      }
    else
      let Level.succ u _ ← getLevel ty | pure ()
      let LOption.some inst ← trySynthInstance (mkApp (mkConst ``ToExpr [u]) ty) | pure ()
      modify fun s => { s with
        unquoted := s.unquoted.addDecl (ldecl.setUserName (addDollar ldecl.userName))
        exprBackSubst := s.exprBackSubst.insert fv (mkApp3 (mkConst ``toExpr [u]) ty inst fv)
        exprSubst := s.exprSubst.insert fv fv
      }

def determineLocalInstances (lctx : LocalContext) : MetaM LocalInstances := do
  let mut localInsts : LocalInstances := {}
  for ldecl in lctx do
    match (← isClass? ldecl.type) with
      | some c => localInsts := localInsts.push { className := c, fvar := ldecl.toExpr }
      | none => pure ()
  pure localInsts

def isLevelFVar (n : Name) : MetaM (Option Expr) := do
  match (← getLCtx).findFromUserName? n with
    | none => pure none
    | some decl =>
      return if ← isDefEq decl.type (mkConst ``Level) then
        some decl.toExpr
      else
        none

abbrev QuoteM := ReaderT UnquoteState MetaM

def quoteLevel : Level → QuoteM Expr
  | Level.zero _ => return mkConst ``levelZero
  | Level.succ u _ => return mkApp (mkConst ``mkLevelSucc) (← quoteLevel u)
  | l@(Level.mvar n _) => throwError "level mvars not supported {l}"
  | Level.max a b _ => return mkApp2 (mkConst ``mkLevelMax) (← quoteLevel a) (← quoteLevel b)
  | Level.imax a b _ => return mkApp2 (mkConst ``mkLevelIMax) (← quoteLevel a) (← quoteLevel b)
  | l@(Level.param n _) => do
    match (← read).levelBackSubst.find? l with
      | some e => return e
      | none =>
        match ← isLevelFVar n with
          | some fv => return fv
          | none =>
            throwError "universe parameter {n} not of type Level"

def quoteLevelList : List Level → QuoteM Expr
  | [] => return mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Level)
  | l::ls => do
    return mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Level)
      (← quoteLevel l) (← quoteLevelList ls)

partial def quoteExpr : Expr → QuoteM Expr
  | Expr.bvar i _ => return mkApp (mkConst ``mkBVar) (toExpr i)
  | e@(Expr.fvar i _) => do
    let some r := (← read).exprBackSubst.find? e | throwError "unknown free variable {e}"
    return r
  | e@(Expr.mvar i _) => throwError "resulting term contains metavariable {e}"
  | Expr.sort u _ => return mkApp (mkConst ``mkSort) (← quoteLevel u)
  | Expr.const n ls _ => return mkApp2 (mkConst ``mkConst) (toExpr n) (← quoteLevelList ls)
  | e@(Expr.app _ _ _) => do
    let fn ← quoteExpr e.getAppFn
    let args ← e.getAppArgs.mapM quoteExpr
    if e.getAppFn.isFVar then -- TODO make configurable
      return mkApp2 (mkConst ``betaRev') fn $
        args.foldl (flip $ mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Expr))
          (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Expr))
    else
      pure $ args.foldl (mkApp2 (mkConst ``mkApp)) fn
  | Expr.lam n t b d => do
    return mkApp4 (mkConst ``mkLambda) (toExpr n.eraseMacroScopes)
      (toExpr d.binderInfo) (← quoteExpr t) (← quoteExpr b)
  | Expr.forallE n t b d => do
    return mkApp4 (mkConst ``mkForall) (toExpr $ if b.hasLooseBVar 0 then n.eraseMacroScopes else Name.anonymous)
      (toExpr d.binderInfo) (← quoteExpr t) (← quoteExpr b)
  | Expr.letE n t v b d => do
    return mkApp5 (mkConst ``mkLet) (toExpr n.eraseMacroScopes) (← quoteExpr t) (← quoteExpr v) (← quoteExpr b) (toExpr d.nonDepLet)
  | Expr.lit l _ => return mkApp (mkConst ``mkLit) (toExpr l)
  | Expr.proj n i e _ => return mkApp3 (mkConst ``mkProj) (toExpr n) (toExpr i) (← quoteExpr e)
  | Expr.mdata mdata e _ => quoteExpr e

def unquoteMVars (mvars : Array MVarId) : UnquoteM (HashMap MVarId Expr × HashMap MVarId (QuoteM Expr)) := do
  let mut exprMVarSubst : HashMap MVarId Expr := HashMap.empty
  let mut mvarSynth : HashMap MVarId (QuoteM Expr) := {}

  unquoteLCtx

  let lctx ← getLCtx
  for mvar in mvars do
    let mdecl := (← getMCtx).getDecl mvar
    if !(lctx.isSubPrefixOf mdecl.lctx && mdecl.lctx.isSubPrefixOf lctx) then
      throwError "incompatible metavariable {mvar.name}\n{MessageData.ofGoal mvar}"

    let ty ← withReducible <| whnf mdecl.type
    let ty ← instantiateMVars ty
    if ty.isAppOf ``QQ then
      let et := ty.getArg! 0
      let newET ← unquoteExpr et
      let newLCtx := (← get).unquoted
      let newLocalInsts ← determineLocalInstances newLCtx
      let exprBackSubst := (← get).exprBackSubst
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts newET
      modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar }
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.insert mvar do
        return mkApp2 (mkConst ``QQ.qq) et (← quoteExpr (← instantiateMVars newMVar))
    else if ty.isSort then
      let u ← mkFreshLevelMVar
      let newLCtx := (← get).unquoted
      let newLocalInsts ← determineLocalInstances newLCtx
      let exprBackSubst := (← get).exprBackSubst
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts (mkSort u)
      modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar }
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.insert mvar do
        return mkApp (mkConst ``QQ) (← quoteExpr (← instantiateMVars newMVar))
    else if ty.isAppOf ``Level then
      let newMVar ← mkFreshLevelMVar
      modify fun s => { s with levelSubst := s.levelSubst.insert (mkMVar mvar) newMVar }
      mvarSynth := mvarSynth.insert mvar do
        quoteLevel (← instantiateLevelMVars newMVar)
    else
      throwError "unsupported type {ty}"

  return (exprMVarSubst, mvarSynth)

def lctxHasMVar : MetaM Bool := do
  (← getLCtx).anyM fun decl => return (← instantiateLocalDeclMVars decl).hasExprMVar

partial def getMVars' (e : Expr) : MetaM (Array MVarId) := go e {}
  where
    go (e : Expr) (mvars : Array MVarId) : MetaM (Array MVarId) := do
      let mut mvars := mvars
      for mvarId in ← getMVars e do
        mvars ← go (← inferType (mkMVar mvarId)) mvars
        unless mvars.contains mvarId do
          mvars := mvars.push mvarId
      return mvars

end Impl

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Impl

def Impl.macro (t : Syntax) (expectedType : Expr) : TermElabM Expr := do
  let lastId := (← mkFreshExprMVar expectedType).mvarId!
  let mvars := (← getMVars' expectedType).push lastId
  let ((exprMVarSubst, mvarSynth), s) ← (unquoteMVars mvars).run {}

  let lastId := (exprMVarSubst.find! mvars.back).mvarId!
  let lastDecl ← Lean.Elab.Term.getMVarDecl lastId

  withLevelNames s.levelNames do
    try resettingSynthInstanceCache do
      withLCtx lastDecl.lctx lastDecl.localInstances do
        let t ← Lean.Elab.Term.elabTerm t lastDecl.type
        let t ← ensureHasType lastDecl.type t
        synthesizeSyntheticMVars false
        if (← logUnassignedUsingErrorInfos (← getMVars t)) then
          throwAbortTerm
        assignExprMVar lastId t
    catch e =>
      if let some n := isAutoBoundImplicitLocalException? e then
        throwError "unsupported implicit auto-bound: {n} is not a level name"
      throw e

    for newLevelName in (← getLevelNames) do
      if s.levelNames.contains newLevelName || (← isLevelFVar newLevelName).isSome then
        pure ()
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

  for mvar in mvars do
    let some synth := mvarSynth.find? mvar | pure ()
    let mvar := mkMVar mvar
    let (true) ← isDefEq mvar (← synth s) | throwError "cannot assign metavariable {mvar}"

  instantiateMVars (mkMVar mvars.back)

scoped elab "q(" t:incQuotDepth(term) ")" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  if expectedType.hasExprMVar then tryPostpone
  ensureHasType expectedType $ ← commitIfDidNotPostpone do
    let mut expectedType ← withReducible <| Impl.whnf expectedType
    if !expectedType.isAppOfArity ``QQ 1 then
      let u ← mkFreshExprMVar (mkConst ``Level)
      let u' := mkApp (mkConst ``mkSort) u
      let t ← mkFreshExprMVar (mkApp (mkConst ``QQ) u')
      expectedType := mkApp (mkConst ``QQ) t
    Impl.macro t expectedType

scoped elab "Q(" t:incQuotDepth(term) ")" : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let (true) ← isDefEq expectedType (mkSort (mkLevelSucc levelZero)) |
    throwError "Q(.) has type Type, expected type is{indentExpr expectedType}"
  commitIfDidNotPostpone do Impl.macro t expectedType


namespace Impl

/-
support `Q($(foo) ∨ False)`
-/

private def push [Monad m] (i t l : Syntax) : StateT (Array $ Syntax × Syntax × Syntax) m Unit :=
  modify fun s => s.push (i, t, l)

partial def floatLevelAntiquot [Monad m] [MonadQuotation m] (stx : Syntax) :
    StateT (Array $ Syntax × Syntax × Syntax) m Syntax :=
  if stx.isAntiquot && !stx.isEscapedAntiquot then
    withFreshMacroScope do
      push (← `(u)) (← `(Level)) (← floatLevelAntiquot stx.getAntiquotTerm)
      `(u)
  else
    match stx with
    | Syntax.node i k args => return Syntax.node i k (← args.mapM floatLevelAntiquot)
    | stx => return stx

partial def floatExprAntiquot [Monad m] [MonadQuotation m] (depth : Nat) :
    Syntax → StateT (Array $ Syntax × Syntax × Syntax) m Syntax
  | stx@`(Q($x)) => do `(Q($(← floatExprAntiquot (depth + 1) x)))
  | stx@`(q($x)) => do `(q($(← floatExprAntiquot (depth + 1) x)))
  | `(Type $term) => do `(Type $(← floatLevelAntiquot term))
  | `(Sort $term) => do `(Sort $(← floatLevelAntiquot term))
  | stx => do
    if stx.isAntiquot && !stx.isEscapedAntiquot then
      let term := stx.getAntiquotTerm
      if depth > 0 then
        return Syntax.mkAntiquotNode (← floatExprAntiquot (depth - 1) term)
      else if term.isIdent && (stripDollars term.getId).isAtomic then
        return addSyntaxDollar term
      else
        withFreshMacroScope do
          push (← `(a)) (← `(QQ _)) term
          return addSyntaxDollar <|<- `(a)
    else
      match stx with
      | Syntax.node i k args => return Syntax.node i k (← args.mapM (floatExprAntiquot depth))
      | stx => pure stx

macro_rules
  | `(Q($t0)) => do
    let (t, lifts) ← floatExprAntiquot 0 t0 #[]
    if lifts.isEmpty && t == t0 then Macro.throwUnsupported
    let mut t ← `(Q($t))
    for (a, ty, lift) in lifts do
      t ← `(let $a:ident : $ty := $lift; $t)
    pure t
  | `(q($t0)) => do
    let (t, lifts) ← floatExprAntiquot 0 t0 #[]
    if lifts.isEmpty && t == t0 then Macro.throwUnsupported
    let mut t ← `(q($t))
    for (a, ty, lift) in lifts do
      t ← `(let $a:ident : $ty := $lift; $t)
    pure t

end Impl
