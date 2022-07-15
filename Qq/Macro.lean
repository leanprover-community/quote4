import Lean
import Qq.ForLean.ReduceEval
import Qq.ForLean.ToExpr
import Qq.Typ
open Lean Meta Std

namespace Qq

namespace Impl

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

@[inline] opaque betaRev' (e : Expr) (revArgs : List Expr) : Expr :=
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
      let .succ u ← getLevel ty | pure ()
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
  | .zero => return mkConst ``Level.zero
  | .succ u => return mkApp (mkConst ``Level.succ) (← quoteLevel u)
  | l@(Level.mvar ..) => throwError "level mvars not supported {l}"
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
    return r
  | e@(.mvar ..) => throwError "resulting term contains metavariable {e}"
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
      let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts newET
      modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar }
      exprMVarSubst := exprMVarSubst.insert mvar newMVar
      mvarSynth := mvarSynth.insert mvar do
        return mkApp2 (mkConst ``QQ.qq) et (← quoteExpr (← instantiateMVars newMVar))
    else if ty.isSort then
      let u ← mkFreshLevelMVar
      let newLCtx := (← get).unquoted
      let newLocalInsts ← determineLocalInstances newLCtx
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

    let refdLevels ← do
      let mut s : CollectLevelParams.State := {}
      for mvar in mvars do
        if let some exprMVar := exprMVarSubst.find? mvar then
          s := s.collect (← instantiateMVars exprMVar)
      pure s.params

    for newLevelName in (← getLevelNames) do
      if let some fvar ← isLevelFVar newLevelName then
        if refdLevels.contains newLevelName then
          addTermInfo' t fvar
      else if (← read).autoBoundImplicit then
        throwAutoBoundImplicitLocal newLevelName
      else
        throwError "unbound level param {newLevelName}"

  for mvar in mvars do
    let some synth := mvarSynth.find? mvar | pure ()
    let mvar := mkMVar mvar
    let (true) ← isDefEq mvar (← synth s) | throwError "cannot assign metavariable {mvar}"

  instantiateMVars (mkMVar mvars.back)

scoped elab "q(" t:term ")" : term <= expectedType => do
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

scoped elab "Q(" t:term ")" : term <= expectedType => do
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
