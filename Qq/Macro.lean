import Lean
import Qq.ForLean.ReduceEval
import Qq.ForLean.ToExpr
import Qq.Typ
open Lean Meta Std

namespace Qq

namespace Impl

inductive ExprBackSubstResult
  | quoted (e : Expr)
  | unquoted (e : Expr)

inductive MVarSynth
  | term (quotedType : Expr) (unquotedMVar : MVarId) --> QQ.qq _ _
  | type (unquotedMVar : MVarId) --> QQ _
  | level (unquotedMVar : LMVarId) --> Level

structure UnquoteState where
  /-- Quoted mvars in the outside lctx (of type `Level`, `QQ _`, or `Type`) -/
  mvars : List (MVarId × MVarSynth) := []

  /- Maps quoted expressions (of type Level) in the old context to level parameter names in the new context -/
  levelSubst : HashMap Expr Level := {}

  /- Maps quoted expressions (of type Expr) in the old context to expressions in the new context -/
  exprSubst : HashMap Expr Expr := {}

  /- New unquoted local context -/
  unquoted := LocalContext.empty

  /- Maps free variables in the new context to expressions in the old context (of type Expr) -/
  exprBackSubst : HashMap Expr ExprBackSubstResult := {}

  /- Maps free variables in the new context to levels in the old context (of type Level) -/
  levelBackSubst : HashMap Level Expr := {}

  levelNames : List Name := []

  mayPostpone : Bool

abbrev UnquoteM := StateT UnquoteState MetaM

abbrev QuoteM := ReaderT UnquoteState MetaM

instance : MonadLift QuoteM UnquoteM where
  monadLift k := do k (← get)

def determineLocalInstances (lctx : LocalContext) : MetaM LocalInstances := do
  let mut localInsts : LocalInstances := {}
  for ldecl in lctx do
    match (← isClass? ldecl.type) with
      | some c => localInsts := localInsts.push { className := c, fvar := ldecl.toExpr }
      | none => pure ()
  pure localInsts

def withUnquotedLCtx [MonadControlT MetaM m] [Monad m] [MonadLiftT QuoteM m] (k : m α) : m α := do
  let unquoted := (← (read : QuoteM _)).unquoted
  withLCtx unquoted (← (determineLocalInstances unquoted : QuoteM _)) k

open Name in
def addDollar : Name → Name
  | anonymous => str anonymous "$"
  | str anonymous s => str anonymous ("$" ++ s)
  | str n s => str (addDollar n) s
  | num n i => num (addDollar n) i

open Name in
def removeDollar : Name → Option Name
  | anonymous => none
  | str anonymous "$" => some anonymous
  | str anonymous s =>
    if s.startsWith "$" then str anonymous (s.drop 1) else none
  | str n s => (removeDollar n).map (str . s)
  | num n i => (removeDollar n).map (num . i)

open Name in
def stripDollars : Name → Name
  | anonymous => anonymous
  | str n "$" => stripDollars n
  | str anonymous s =>
    let s := s.dropWhile (· = '$')
    if s = "" then anonymous else str anonymous s
  | str n s => str (stripDollars n) s
  | num n i => num (stripDollars n) i

def addSyntaxDollar : Syntax → Syntax
  | .ident info rawVal            val  preresolved =>
    .ident info rawVal (addDollar val) preresolved
  | stx => panic! s!"addSyntaxDollar {stx}"

def mkAbstractedLevelName (e : Expr) : MetaM Name :=
  return e.getAppFn.constName?.getD `udummy ++ (← mkFreshId)

def isBad (e : Expr) : Bool := Id.run do
  if let .const (.str _ "rec") _ := e.getAppFn then
    return true
  return false

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/How.20to.20WHNF.20without.20exposing.20recursors.3F/near/249743042
partial def whnf (e : Expr) (e0 : Expr := e) : MetaM Expr := do
  let e ← whnfCore e
  let e0 := if isBad e then e0 else e
  match ← unfoldDefinition? e with
    | some e => whnf e (if isBad e then e0 else e)
    | none => pure e0

def whnfR (e : Expr) : MetaM Expr :=
  withReducible (whnf e)

mutual

partial def unquoteLevel (e : Expr) : UnquoteM Level := do
  let e ← whnf e
  if let some l := (← get).levelSubst.find? e then
    return l
  if e.isAppOfArity ``Level.zero 0 then pure levelZero
  else if e.isAppOfArity ``Level.succ 1 then return mkLevelSucc (← unquoteLevel (e.getArg! 0))
  else if e.isAppOfArity ``Level.max 2 then return mkLevelMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.imax 2 then return mkLevelIMax (← unquoteLevel (e.getArg! 0)) (← unquoteLevel (e.getArg! 1))
  else if e.isAppOfArity ``Level.param 1 then return mkLevelParam (← reduceEval (e.getArg! 0))
  else if e.isAppOfArity ``Level.mvar 1 then return mkLevelMVar (← reduceEval (e.getArg! 0))
  else
    if let .mvar mvarId := e.getAppFn then
      if !(← mvarId.isAssignable) && (← get).mayPostpone then Elab.throwPostpone
      let e' ← mkFreshExprMVar (mkConst ``Level)
      if ← isDefEq e e' then
        return ← unquoteLevelMVar e'.mvarId!
    let name ← mkAbstractedLevelName e
    let l := mkLevelParam name
    modify fun s => { s with
      levelSubst := s.levelSubst.insert e l
      levelBackSubst := s.levelBackSubst.insert l e
    }
    pure l

partial def unquoteLevelMVar (mvar : MVarId) : UnquoteM Level := do
  let newMVar ← mkFreshLevelMVar
  modify fun s => { s with
    levelSubst := s.levelSubst.insert (.mvar mvar) newMVar
    levelBackSubst := s.levelBackSubst.insert newMVar (.mvar mvar)
    mvars := (mvar, .level newMVar.mvarId!) :: s.mvars
  }
  return newMVar

end

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

@[inline] opaque betaRev' (e : Expr) (revArgs : List Expr) : Expr :=
  e.betaRev revArgs.toArray

def makeZetaReduce (a : FVarId) (b : Expr) : MetaM (Option LocalContext) := do
  let .cdecl aIdx aFVarId aUserName aType _ aKind ← a.getDecl | return none
  let bFVars := (← b.collectFVars.run {}).2
  let toRevert := (← collectForwardDeps #[.fvar a] (preserveOrder := true)).map (·.fvarId!)
  for y in toRevert do if bFVars.fvarSet.contains y then return none
  let oldLCtx ← getLCtx
  let newLCtx := toRevert.foldl (init := oldLCtx) (·.erase ·)
  let newLCtx := newLCtx.addDecl <| .ldecl aIdx aFVarId aUserName aType b (nonDep := false) aKind
  let newLCtx := toRevert.filter (· != a) |>.foldl (init := newLCtx) (·.addDecl <| oldLCtx.get! ·)
  return newLCtx

def makeDefEq (a b : Expr) : MetaM (Option LocalContext) := do
  if let .fvar a ← whnf a then if let some lctx ← makeZetaReduce a b then return lctx
  if let .fvar b ← whnf b then if let some lctx ← makeZetaReduce b a then return lctx
  return none

mutual

partial def unquoteExprList (e : Expr) : UnquoteM (List Expr) := do
  let e ← whnf e
  if e.isAppOfArity ``List.nil 1 then
    pure []
  else if e.isAppOfArity ``List.cons 3 then
    return (← unquoteExpr (e.getArg! 1)) :: (← unquoteExprList (e.getArg! 2))
  else
    throwFailedToEval e

partial def unquoteExprMVar (mvarId : MVarId) : UnquoteM Expr := do
  have mvar := .mvar mvarId
  let ty ← instantiateMVars (← whnfR (← inferType mvar))
  unless ty.isAppOf ``QQ do throwError "not of type Q(_):{indentExpr ty}"
  have et := ty.getArg! 0
  let newET ← unquoteExpr et
  let newMVar ← withUnquotedLCtx do mkFreshExprMVar newET
  modify fun s => { s with
    exprSubst := s.exprSubst.insert mvar newMVar
    exprBackSubst := s.exprBackSubst.insert newMVar (.quoted mvar)
    mvars := (mvarId, .term et newMVar.mvarId!) :: s.mvars
  }
  return newMVar

partial def unquoteExpr (e : Expr) : UnquoteM Expr := do
  if e.isAppOfArity ``QQ.qq 2 then return ← unquoteExpr (e.getArg! 1)
  if e.isAppOfArity ``toExpr 3 then return e.getArg! 2
  let e ← instantiateMVars (← whnf e)
  let eTy ← whnfR (← inferType e)
  if eTy.isAppOfArity ``QQ 1 then
    if let some e' := (← get).exprSubst.find? e then
      return e'
    if let .mvar mvarId := e.getAppFn then
      if !(← mvarId.isAssignable) then
        if (← get).mayPostpone then
          Elab.throwPostpone
      else
        let e' ← mkFreshExprMVar eTy
        if ← isDefEq e e' then
          return ← unquoteExprMVar e'.mvarId!
    let ty ← unquoteExpr (eTy.getArg! 0)
    let fvarId := FVarId.mk (← mkFreshId)
    let name ← mkAbstractedName e
    let fv := mkFVar fvarId
    modify fun s => { s with
      unquoted := s.unquoted.mkLocalDecl fvarId name ty
      exprSubst := s.exprSubst.insert e fv
      exprBackSubst := s.exprBackSubst.insert fv (.quoted e)
    }
    return fv
  let e ← whnf e
  let .const c _ ← pure e.getAppFn | throwError "unquoteExpr: {e} : {eTy}"
  let nargs := e.getAppNumArgs
  match c, nargs with
    | ``betaRev', 2 => return betaRev' (← unquoteExpr (e.getArg! 0)) (← unquoteExprList (e.getArg! 1))
    | ``Expr.bvar, 1 => return .bvar (← reduceEval (e.getArg! 0))
    /- | ``Expr.fvar, 2 => mkFVar (← reduceEval (e.getArg! 0)) -/
    /- | ``Expr.mvar, 2 => mkMVar (← reduceEval (e.getArg! 0)) -/
    | ``Expr.sort, 1 => return .sort (← unquoteLevel (e.getArg! 0))
    | ``Expr.const, 2 => return .const (← reduceEval (e.getArg! 0)) (← unquoteLevelList (e.getArg! 1))
    | ``Expr.app, 2 => return .app (← unquoteExpr (e.getArg! 0)) (← unquoteExpr (e.getArg! 1))
    | ``Expr.lam, 4 =>
      return .lam (← reduceEval (e.getArg! 0))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
        (← reduceEval (e.getArg! 3))
    | ``Expr.forallE, 4 =>
      return .forallE (← reduceEval (e.getArg! 0))
        (← unquoteExpr (e.getArg! 1))
        (← unquoteExpr (e.getArg! 2))
        (← reduceEval (e.getArg! 3))
    | ``Expr.letE, 5 =>
      return .letE (← reduceEval (e.getArg! 0)) (← unquoteExpr (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
        (← unquoteExpr (e.getArg! 3)) (← reduceEval (e.getArg! 4))
    | ``Expr.lit, 1 => return .lit (← reduceEval (e.getArg! 0))
    | ``Expr.proj, 3 =>
      return .proj (← reduceEval (e.getArg! 0)) (← reduceEval (e.getArg! 1)) (← unquoteExpr (e.getArg! 2))
    | _, _ => throwError "unquoteExpr: {e} : {eTy}"

end

partial def unquoteLCtx : UnquoteM Unit := do
  for ldecl in (← getLCtx) do
    let fv := ldecl.toExpr
    let ty := ldecl.type
    let whnfTy ← withReducible <| whnf ty
    if whnfTy.isAppOfArity ``QQ 1 then
      let qTy := whnfTy.appArg!
      let newTy ← unquoteExpr qTy
      modify fun s => { s with
        unquoted := s.unquoted.addDecl $
          LocalDecl.cdecl ldecl.index ldecl.fvarId (addDollar ldecl.userName) newTy ldecl.binderInfo ldecl.kind
        exprBackSubst := s.exprBackSubst.insert fv (.quoted fv)
        exprSubst := s.exprSubst.insert fv fv
      }
    else if whnfTy.isAppOfArity ``QE 4 then
      let tyLevel ← unquoteLevel (whnfTy.getArg! 0)
      let ty ← unquoteExpr (whnfTy.getArg! 1)
      let lhs ← unquoteExpr (whnfTy.getArg! 2)
      let rhs ← unquoteExpr (whnfTy.getArg! 3)
      let eqTy := mkApp3 (.const ``Eq [tyLevel]) ty lhs rhs
      let unquoted := (← get).unquoted
      let unquoted := unquoted.addDecl <|
        .cdecl ldecl.index ldecl.fvarId (addDollar ldecl.userName) eqTy ldecl.binderInfo ldecl.kind
      let unquoted := (← withUnquotedLCtx do makeDefEq lhs rhs).getD unquoted
      modify fun s => { s with
        unquoted
        exprBackSubst := s.exprBackSubst.insert fv (.unquoted (mkApp2 (.const ``Eq.refl [tyLevel]) ty lhs))
        -- exprSubst := s.exprSubst.insert fv fv
      }
    else if whnfTy.isAppOfArity ``Level 0 then
      modify fun s => { s with
        levelNames := ldecl.userName :: s.levelNames
        levelSubst := s.levelSubst.insert fv (mkLevelParam ldecl.userName)
      }
    else
      let .succ u ← getLevel ty | pure ()
      let LOption.some inst ← trySynthInstance (mkApp (mkConst ``ToExpr [u]) ty) | pure ()
      modify fun s => { s with
        unquoted := s.unquoted.addDecl (ldecl.setUserName (addDollar ldecl.userName))
        exprBackSubst := s.exprBackSubst.insert fv (.quoted (mkApp3 (mkConst ``toExpr [u]) ty inst fv))
        exprSubst := s.exprSubst.insert fv fv
      }

def isLevelFVar (n : Name) : MetaM (Option Expr) := do
  match (← getLCtx).findFromUserName? n with
    | none => pure none
    | some decl =>
      return if ← isDefEq decl.type (mkConst ``Level) then
        some decl.toExpr
      else
        none

def quoteLevel : Level → QuoteM Expr
  | .zero => return mkConst ``Level.zero
  | .succ u => return mkApp (mkConst ``Level.succ) (← quoteLevel u)
  | l@(.mvar ..) => do
    if let some e := (← read).levelBackSubst.find? l then
      return e
    throwError "cannot quote level mvar {l}"
  | .max a b => return mkApp2 (mkConst ``Level.max) (← quoteLevel a) (← quoteLevel b)
  | .imax a b => return mkApp2 (mkConst ``Level.imax) (← quoteLevel a) (← quoteLevel b)
  | l@(.param n) => do
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
  | .bvar i => return mkApp (mkConst ``Expr.bvar) (toExpr i)
  | e@(.fvar ..) => do
    let some r := (← read).exprBackSubst.find? e | throwError "unknown free variable {e}"
    match r with
    | .quoted r => return r
    | .unquoted r => quoteExpr r
  | e@(.mvar ..) => do
    if let some (.quoted r) := (← read).exprBackSubst.find? e then return r
    throwError "resulting term contains metavariable {e}"
  | .sort u => return mkApp (mkConst ``Expr.sort) (← quoteLevel u)
  | .const n ls => return mkApp2 (mkConst ``Expr.const) (toExpr n) (← quoteLevelList ls)
  | e@(.app _ _) => do
    let fn ← quoteExpr e.getAppFn
    let args ← e.getAppArgs.mapM quoteExpr
    if e.getAppFn.isFVar then -- TODO make configurable
      return mkApp2 (mkConst ``betaRev') fn $
        args.foldl (flip $ mkApp3 (mkConst ``List.cons [levelZero]) (mkConst ``Expr))
          (mkApp (mkConst ``List.nil [levelZero]) (mkConst ``Expr))
    else
      pure $ args.foldl (mkApp2 (mkConst ``Expr.app)) fn
  | .lam n t b d => do
    return mkApp4 (mkConst ``Expr.lam) (toExpr n.eraseMacroScopes)
      (← quoteExpr t) (← quoteExpr b) (toExpr d)
  | .forallE n t b d => do
    return mkApp4 (mkConst ``Expr.forallE) (toExpr $ if b.hasLooseBVar 0 then n.eraseMacroScopes else Name.anonymous)
      (← quoteExpr t) (← quoteExpr b) (toExpr d)
  | .letE n t v b d => do
    return mkApp5 (mkConst ``Expr.letE) (toExpr n.eraseMacroScopes) (← quoteExpr t) (← quoteExpr v) (← quoteExpr b) (toExpr d)
  | .lit l => return mkApp (mkConst ``Expr.lit) (toExpr l)
  | .proj n i e => return mkApp3 (mkConst ``Expr.proj) (toExpr n) (toExpr i) (← quoteExpr e)
  | .mdata _ e => quoteExpr e

def unquoteMVarCore (mvarId : MVarId) : UnquoteM Unit := do
  have mvar := .mvar mvarId
  let ty ← instantiateMVars (← whnfR (← inferType mvar))
  if ty.isAppOf ``QQ then
    _ ← unquoteExprMVar mvarId
  else if ty.isAppOf ``Level then
    _ ← unquoteLevelMVar mvarId
  else if ty.isSort then
    let newMVar ← withUnquotedLCtx do mkFreshTypeMVar
    modify fun s => { s with
      exprSubst := s.exprSubst.insert mvar newMVar
      exprBackSubst := s.exprBackSubst.insert newMVar (.quoted mvar)
      mvars := (mvar.mvarId!, .type newMVar.mvarId!) :: s.mvars
    }
  else
    throwError "unsupported expected type for quoted expression{indentExpr ty}"

def unquoteMVar (mvar : Expr) : UnquoteM Unit := do
  unquoteLCtx
  unquoteMVarCore mvar.mvarId!

def MVarSynth.isAssigned : MVarSynth → MetaM Bool
  | .term _ newMVar => newMVar.isAssigned
  | .type newMVar => newMVar.isAssigned
  | .level newMVar => isLevelMVarAssigned newMVar

def MVarSynth.synth : MVarSynth → QuoteM Expr
  | .term et newMVar => return mkApp2 (mkConst ``QQ.qq) et (← quoteExpr (← instantiateMVars (.mvar newMVar)))
  | .type newMVar => return mkApp (mkConst ``QQ) (← quoteExpr (← instantiateMVars (.mvar newMVar)))
  | .level newMVar => do quoteLevel (← instantiateLevelMVars (.mvar newMVar))

def lctxHasMVar : MetaM Bool := do
  (← getLCtx).anyM fun decl => return (← instantiateLocalDeclMVars decl).hasExprMVar

end Impl

open Lean.Elab Lean.Elab.Tactic Lean.Elab.Term Impl

@[specialize]
def withProcessPostponed [Monad m] [MonadFinally m] [MonadLiftT MetaM m] (k : m α) : m α := do
  let postponed ← getResetPostponed
  try
    k <* discard (processPostponed (mayPostpone := false) (exceptionOnFailure := true))
  finally
    setPostponed (postponed ++ (← getPostponed))

def Impl.macro (t : Syntax) (expectedType : Expr) : TermElabM Expr := do
  let mainMVar ← mkFreshExprMVar expectedType
  let s ← (unquoteMVar mainMVar *> get).run' { mayPostpone := (← read).mayPostpone }

  have lastId := match s.mvars with
    | (_, .term _ lastMVar) :: _ | (_, .type lastMVar) :: _ => lastMVar
    | _ => unreachable!
  let lastDecl ← lastId.getDecl

  withLevelNames s.levelNames do
    try
      withRef t do
      withLCtx lastDecl.lctx lastDecl.localInstances do
      withProcessPostponed do
      withSynthesize do
        let t ← Term.elabTerm t lastDecl.type
        let t ← ensureHasType lastDecl.type t
        synthesizeSyntheticMVars (mayPostpone := false)
        if (← logUnassignedUsingErrorInfos (← getMVars t)) then
          throwAbortTerm
        lastId.assign t
    catch e =>
      if let some n := isAutoBoundImplicitLocalException? e then
        throwError "unsupported implicit auto-bound: {n} is not a level name"
      throw e

    let refdLevels ← do
      let mut lvls : CollectLevelParams.State := {}
      for (_, synth) in s.mvars do
        match synth with
        | .term _ exprMVar | .type exprMVar =>
          lvls := lvls.collect (← instantiateMVars (.mvar exprMVar))
        | _ => pure ()
      pure lvls.params

    for newLevelName in (← getLevelNames) do
      if let some fvar ← isLevelFVar newLevelName then
        if refdLevels.contains newLevelName then
          addTermInfo' t fvar
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

  for (mvar, synth) in s.mvars.reverse do
    let mvar := mkMVar mvar
    if ← synth.isAssigned then
      let t ← synth.synth s
      unless ← isDefEq mvar t do
        throwError "cannot assign metavariable ({mvar} : {← inferType mvar}) with {t}"

  instantiateMVars mainMVar

scoped syntax "q(" term Parser.Term.optType ")" : term

macro_rules | `(q($t : $ty)) => `(q(($t : $ty)))

elab_rules : term <= expectedType
  | `(q($t)) => do
    let expectedType ← instantiateMVars expectedType
    if expectedType.hasExprMVar then tryPostpone
    if ← lctxHasMVar then tryPostpone
    ensureHasType expectedType $ ← commitIfDidNotPostpone do
      let mut expectedType ← withReducible <| Impl.whnf expectedType
      if !expectedType.isAppOfArity ``QQ 1 then
        let u ← mkFreshExprMVar (mkConst ``Level)
        let u' := mkApp (mkConst ``mkSort) u
        let t ← mkFreshExprMVar (mkApp (mkConst ``QQ) u')
        expectedType := mkApp (mkConst ``QQ) t
      Impl.macro t expectedType

scoped syntax "Q(" term Parser.Term.optType ")" : term

macro_rules | `(Q($t : $ty)) => `(Q(($t : $ty)))

elab_rules : term <= expectedType
  | `(Q($t)) => do
    let expectedType ← instantiateMVars expectedType
    let (true) ← isDefEq expectedType (mkSort (mkLevelSucc levelZero)) |
      throwError "Q(.) has type Type, expected type is{indentExpr expectedType}"
    commitIfDidNotPostpone do Impl.macro t expectedType

scoped notation a:50 " =Q " b:51 => QE q(a) q(b)

namespace Impl

/-
support `Q($(foo) ∨ False)`
-/

private def push [Monad m] (i t l : Syntax) : StateT (Array $ Syntax × Syntax × Syntax) m Unit :=
  modify fun s => s.push (i, t, l)

partial def floatLevelAntiquot' [Monad m] [MonadQuotation m] (stx : Syntax) :
    StateT (Array $ Syntax × Syntax × Syntax) m Syntax :=
  if stx.isAntiquot && !stx.isEscapedAntiquot then
    withFreshMacroScope do
      push (← `(u)) (← `(Level)) (← floatLevelAntiquot' stx.getAntiquotTerm)
      `(u)
  else
    match stx with
    | Syntax.node i k args => return Syntax.node i k (← args.mapM floatLevelAntiquot')
    | stx => return stx

open TSyntax.Compat in
partial def floatExprAntiquot' [Monad m] [MonadQuotation m] (depth : Nat) :
    Syntax → StateT (Array $ Syntax × Syntax × Syntax) m Syntax
  | `(Q($x)) => do `(Q($(← floatExprAntiquot' (depth + 1) x)))
  | `(q($x)) => do `(q($(← floatExprAntiquot' (depth + 1) x)))
  | `(Type $term) => do `(Type $(← floatLevelAntiquot' term))
  | `(Sort $term) => do `(Sort $(← floatLevelAntiquot' term))
  | stx => do
    if let (some (kind, _pseudo), false) := (stx.antiquotKind?, stx.isEscapedAntiquot) then
      let term := stx.getAntiquotTerm
      if depth > 0 then
        return Syntax.mkAntiquotNode kind (← floatExprAntiquot' (depth - 1) term)
      else if term.isIdent && (stripDollars term.getId).isAtomic then
        return addSyntaxDollar term
      else
        withFreshMacroScope do
          push (← `(a)) (← `(QQ _)) term
          return addSyntaxDollar <|<- `(a)
    else
      match stx with
      | Syntax.node i k args => return Syntax.node i k (← args.mapM (floatExprAntiquot' depth))
      | stx => pure stx

open TSyntax.Compat in
partial def floatExprAntiquot [Monad m] [MonadQuotation m] (depth : Nat) :
    Term → StateT (Array $ Ident × Term × Term) m Term :=
  fun t s => do
    let (t, lifts) ← floatExprAntiquot' depth t (s.map fun (a,t,l) => (a,t,l))
    return (t, lifts.map fun (a,t,l) => (a,t,l))

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
