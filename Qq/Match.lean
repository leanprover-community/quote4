import Qq.Macro
import Qq.MetaM
import Qq.ForLean.Do
import Qq.SortLocalDecls
/-!
# `~q()` matching

This file extends the syntax of `match` and `let` to permit matching terms of type `Q(α)` using
`~q(<pattern>)`, just as terms of type `Syntax` can be matched with `` `(<pattern>) ``.
Compare to the builtin `match_expr` and `let_expr`, `~q()` matching:
* is type-safe, and so helps avoid many mistakes in match patterns
* matches by definitional equality, rather than expression equality
* supports compound expressions, not just a single application

See `Qq.matcher` for a brief syntax summary.

## Matching typeclass instances

For a more complete example, consider
```
def isCanonicalAdd {u : Level} {α : Q(Type u)} (inst : Q(Add $α)) (x : Q($α)) :
    MetaM <| Option (Q($α) × Q($α)) := do
  match x with
  | ~q($a + $b) => return some (a, b)
  | _ => return none
```
Here, the `~q($a + $b)` match is specifically matching the addition against the provided `inst`
instance, as this is what is being used to elaborate the `+`.

If the intent is to match an _arbitrary_ `Add α` instance in `x`,
then you must match this with a `$inst` antiquotation:
```
def isAdd {u : Level} {α : Q(Type u)} (x : Q($α)) :
    MetaM <| Option (Q(Add $α) × Q($α) × Q($α)) := do
  match x with
  | ~q(@HAdd.hAdd _ _ _ (@instHAdd _ $inst) $a $b) => return some (inst, a, b)
  | _ => return none
```

## Matching `Expr`s

By itself, `~q()` can only match against terms of the form `Q($α)`.
To match an `Expr`, it must first be converted to Qq with `Qq.inferTypeQ`.

For instance, to match an arbitrary expression for `n + 37` where `n : Nat`,
we can write
```
def isAdd37 (e : Expr) : MetaM (Option Q(Nat)) := do
  let ⟨1, ~q(Nat), ~q($n + 37)⟩ ← inferTypeQ e | return none
  return some n
```
This is performing three sequential matches: first that `e` is in `Sort 1`,
then that the type of `e` is `Nat`,
then finally that `e` is of the right form.
This syntax can be used in `match` too.
-/

open Lean in
partial def Lean.Syntax.stripPos : Syntax → Syntax
  | atom _ a => atom .none a
  | ident _ r v p => ident .none r v p
  | node _ kind args => node .none kind (args.map stripPos)
  | missing => missing

open Lean Elab Term Meta
open Parser.Term

namespace Qq

namespace Impl

structure PatVarDecl where
  ty : Option Q(Expr)
  fvarId : FVarId
  userName : Name

def PatVarDecl.fvarTy : PatVarDecl → Q(Type)
  | { ty := none, .. } => q(Level)
  | { ty := some _, .. } => q(Expr)

def PatVarDecl.fvar (decl : PatVarDecl) : Q($((decl.fvarTy))) :=
  Expr.fvar decl.fvarId

def mkIsDefEqType : List PatVarDecl → Q(Type)
  | [] => q(Bool)
  | decl :: decls => q($(decl.fvarTy) × $(mkIsDefEqType decls))

def mkIsDefEqResult (val : Bool) : (decls : List PatVarDecl) → Q($(mkIsDefEqType decls))
  | [] => show Q(Bool) from q($val)
  | decl :: decls => q(($(decl.fvar), $(mkIsDefEqResult val decls)))

def mkIsDefEqResultVal : (decls : List PatVarDecl) → Q($(mkIsDefEqType decls)) → Q(Bool)
  | [], val => q($val)
  | _ :: decls, val => mkIsDefEqResultVal decls q($val.2)

def mkLambda' (n : Name) (fvar : Expr) (ty : Expr) (body : Expr) : MetaM Expr :=
  return mkLambda n BinderInfo.default ty (← body.abstractM #[fvar])

def mkLet' (n : Name) (fvar : Expr) (ty : Expr) (val : Expr) (body : Expr) : MetaM Expr :=
  return mkLet n ty val (← body.abstractM #[fvar])

def mkLambdaQ (n : Name) (fvar : Quoted α) (body : Quoted β) : MetaM (Quoted (mkForall n BinderInfo.default α β)) :=
  return mkLambda n BinderInfo.default α (← body.abstractM #[fvar])

def mkInstantiateMVars (decls : List PatVarDecl) : List PatVarDecl → MetaM Q(MetaM $(mkIsDefEqType decls))
  | [] => return q(return $(mkIsDefEqResult true decls))
  -- https://github.com/leanprover/lean4/issues/501
  | { ty := none, fvarId := fvarId, userName := userName } :: rest => do
    let decl : PatVarDecl := { ty := none, fvarId := fvarId, userName := userName }
    let instMVars : Q(Level → MetaM $(mkIsDefEqType decls)) ←
      mkLambdaQ _ decl.fvar q($(← mkInstantiateMVars decls rest))
    return q(Bind.bind (instantiateLevelMVars $(decl.fvar)) $instMVars)
  | { ty := some ty, fvarId := fvarId, userName := userName } :: rest => do
    let decl : PatVarDecl := { ty := some ty, fvarId := fvarId, userName := userName }
    let instMVars : Q(Expr → MetaM $(mkIsDefEqType decls)) ←
      mkLambdaQ _ decl.fvar q($(← mkInstantiateMVars decls rest))
    return q(Bind.bind (instantiateMVars $(decl.fvar)) $instMVars)

def mkIsDefEqCore (decls : List PatVarDecl) (pat discr : Q(Expr)) :
    List PatVarDecl → MetaM Q(MetaM $(mkIsDefEqType decls))
  | { ty := none, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := none, fvarId := fvarId, userName := userName }
    return q(Bind.bind mkFreshLevelMVar $(← mkLambdaQ `x decl.fvar (← mkIsDefEqCore decls pat discr rest)))
  | { ty := some ty, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := some ty, fvarId := fvarId, userName := userName }
    return q(Bind.bind (mkFreshExprMVar $ty) $(← mkLambdaQ `x decl.fvar (← mkIsDefEqCore decls pat discr rest)))
  | [] => do
    let instMVars ← mkInstantiateMVars decls decls
    return q(do
      let matches? ← withReducible $ isDefEq $pat $discr
      (if matches? then $instMVars else return $(mkIsDefEqResult false decls)))

def mkIsDefEq (decls : List PatVarDecl) (pat discr : Q(Expr)) : MetaM Q(MetaM $(mkIsDefEqType decls)) := do
  return q(withNewMCtxDepth $(← mkIsDefEqCore decls pat discr decls))

def withLetHave [Monad m] [MonadControlT MetaM m] [MonadLiftT MetaM m] [MonadLCtx m]
    (fvarId : FVarId) (userName : Name) (val : (Quoted α)) (k : (Quoted α) → m (Quoted β)) : m (Quoted β) := do
  withExistingLocalDecls [LocalDecl.cdecl default fvarId userName α .default .default] do
    return Quoted.unsafeMk $ ← mkLet' userName (.fvar fvarId) α val (← k (.fvar fvarId))

def mkQqLets {γ : Q(Type)} : (decls : List PatVarDecl) → Q($(mkIsDefEqType decls)) →
    TermElabM Q($γ) → TermElabM Q($γ)
  | { ty := none, fvarId := fvarId, userName := userName } :: decls, acc, cb =>
    withLetHave fvarId userName (α := q(Level)) q($acc.1) fun _ => mkQqLets decls q($acc.2) cb
  | { ty := some ty, fvarId := fvarId, userName := userName } :: decls, acc, cb =>
    withLetHave fvarId userName (α := q(Quoted $ty)) q($acc.1) fun _ => mkQqLets decls q($acc.2) cb
  | [], _, cb => cb

-- FIXME: we're reusing fvarids here
def replaceTempExprsByQVars : List PatVarDecl → Expr → Expr
  | [], e => e
  | { ty := some _, fvarId, .. } :: decls, e =>
    ((replaceTempExprsByQVars decls e).abstract #[.fvar fvarId]).instantiate #[.fvar fvarId]
  | { ty := none, .. } :: decls, e =>
    replaceTempExprsByQVars decls e

def makeMatchCode {γ : Q(Type)} {m : Q(Type → Type v)} (_instLift : Q(MonadLiftT MetaM $m)) (_instBind : Q(Bind $m))
    (decls : List PatVarDecl) (uTy : Q(Level)) (ty : Q(Quoted (.sort $uTy)))
    (pat discr : Q(Quoted $ty)) (alt : Q($m $γ)) (expectedType : Expr)
    (k : Expr → TermElabM Q($m $γ)) : TermElabM Q($m $γ) := do
  let nextDecls : List PatVarDecl :=
    decls.map fun decl => { decl with ty := decl.ty.map fun e => replaceTempExprsByQVars decls e }
  let next ← withLocalDeclD (← mkFreshBinderName) (mkIsDefEqType decls) fun fv => do
    let fv : Q($(mkIsDefEqType decls)) := fv
    -- note: cannot inline into `$body` due to leanprover/lean4#3827
    let body ← mkQqLets nextDecls fv do
      have pat : Q(Quoted $ty) := replaceTempExprsByQVars decls pat
      let (_, s) ← unquoteLCtx.run { mayPostpone := (← read).mayPostpone }
      let _discr' ← (unquoteExpr discr).run' s
      let _pat' ← (unquoteExpr pat).run' s
      withLocalDeclDQ (← mkFreshUserName `match_eq) q(QuotedDefEq $discr $pat) fun h => do
        let res ← k expectedType
        let res : Q($m $γ) ← instantiateMVars res
        let res : Q($m $γ) := (← res.abstractM #[h]).instantiate #[q(⟨⟩ : QuotedDefEq $discr $pat)]
        return res
    let next : Q($m $γ) :=
      q(if $(mkIsDefEqResultVal decls fv) then
          $body
        else
          $alt)
    return show Q($(mkIsDefEqType decls) → $m $γ) from
      Quoted.unsafeMk $ ← mkLambda' `result fv (mkIsDefEqType decls) next
  pure q(Bind.bind $(← mkIsDefEq decls pat discr) $next)

def unquoteForMatch (et : Expr) : UnquoteM (LocalContext × LocalInstances × Expr) := do
  unquoteLCtx
  let newET ← unquoteExpr et
  let newLCtx := (← get).unquoted
  return (newLCtx, ← determineLocalInstances newLCtx, newET)

def mkNAryFunctionType : Nat → MetaM Expr
  | 0 => mkFreshTypeMVar
  | n+1 => do withLocalDeclD `x (← mkFreshTypeMVar) fun x => do
    mkForallFVars #[x] (← mkNAryFunctionType n)

structure PatternVar where
  name : Name
  /-- Pattern variables can be functions; if so, this is their arity. -/
  arity : Nat
  mvar : Expr
  stx : Term

partial def getPatVars (pat : Term) : StateT (Array PatternVar) TermElabM Term := do
  match pat with
    | `($fn $args*) => if isPatVar fn then return ← mkMVar fn args
    | _ => if isPatVar pat then return ← mkMVar pat #[]
  match pat with
    | ⟨.node info kind args⟩ => return ⟨.node info kind (← args.mapM (getPatVars ⟨·⟩))⟩
    | pat => return pat

  where

    isPatVar (fn : Syntax) : Bool :=
      fn.isAntiquot && !fn.isEscapedAntiquot && fn.getAntiquotTerm.isIdent &&
      fn.getAntiquotTerm.getId.isAtomic

    mkMVar (fn : Syntax) (args : Array Term) : StateT _ TermElabM Term := do
      let args ← args.mapM getPatVars
      let id := fn.getAntiquotTerm.getId
      withFreshMacroScope do
        if let some p := (← get).find? fun p => p.name == id then
          return ← `($(p.stx) $args*)
        let mvar ← elabTerm (← `(?m)).1.stripPos (← mkNAryFunctionType args.size)
        modify (·.push ⟨id, args.size, mvar, ← `(?m)⟩)
        `(?m $args*)
def elabPat (pat : Term) (lctx : LocalContext) (localInsts : LocalInstances) (ty : Expr)
    (levelNames : List Name) : TermElabM (Expr × Array LocalDecl × Array Name) :=
  withLCtx lctx localInsts do
    withLevelNames levelNames do
          let (pat, patVars) ← getPatVars pat #[]
          let pat ← Lean.Elab.Term.elabTerm pat ty
          let pat ← ensureHasType ty pat
          synthesizeSyntheticMVars (postpone := .no)
          let pat ← instantiateMVars pat

          let mctx ← getMCtx
          let levelNames ← getLevelNames
          let r := mctx.levelMVarToParam levelNames.elem (fun _ => false) pat `u 1
          setMCtx r.mctx

          let mut newDecls := #[]

          for patVar in patVars do
            assert! patVar.mvar.isMVar
            let fvarId := FVarId.mk (← mkFreshId)
            let type ← inferType patVar.mvar
            newDecls := newDecls.push $
              LocalDecl.cdecl default fvarId patVar.name type .default .default
            patVar.mvar.mvarId!.assign (.fvar fvarId)

          for newMVar in ← getMVars pat do
            let fvarId := FVarId.mk (← mkFreshId)
            let type ← instantiateMVars (← newMVar.getDecl).type
            let userName ← mkFreshBinderName
            newDecls := newDecls.push $
              LocalDecl.cdecl default fvarId userName type .default .default
            newMVar.assign (.fvar fvarId)

          withExistingLocalDecls newDecls.toList do
            return (← instantiateMVars pat,
              ← sortLocalDecls (← newDecls.mapM fun d => instantiateLocalDeclMVars d),
              r.newParamNames)

scoped elab "_qq_match" pat:term " ← " e:term " | " alt:term " in " body:term : term <= expectedType => do
  let emr ← extractBind expectedType
  let alt ← elabTermEnsuringType alt expectedType

  let argLvlExpr ← mkFreshExprMVarQ q(Level)
  let argTyExpr ← mkFreshExprMVarQ q(Quoted (.sort $argLvlExpr))
  let e' ← elabTermEnsuringTypeQ e q(Quoted $argTyExpr)
  let argTyExpr ← instantiateMVarsQ argTyExpr

  let ((lctx, localInsts, type), s) ← (unquoteForMatch argTyExpr).run { mayPostpone := (← read).mayPostpone }
  let (pat, patVarDecls, newLevels) ← elabPat pat lctx localInsts type s.levelNames

  let mut s := s
  let mut oldPatVarDecls : List PatVarDecl := []
  for newLevel in newLevels do
    let fvarId := FVarId.mk (← mkFreshId)
    oldPatVarDecls := oldPatVarDecls ++ [{ ty := none, fvarId := fvarId, userName := newLevel }]
    s := { s with levelBackSubst := s.levelBackSubst.insert (.param newLevel) (.fvar fvarId) }

  for ldecl in patVarDecls do
    let qty ← (quoteExpr ldecl.type).run s
    oldPatVarDecls := oldPatVarDecls ++ [{ ty := some qty, fvarId := ldecl.fvarId, userName := ldecl.userName }]
    s := { s with exprBackSubst := s.exprBackSubst.insert ldecl.toExpr (.quoted ldecl.toExpr) }

  have m : Q(Type → Type) := emr.m
  have γ : Q(Type) := emr.returnType
  let inst ← synthInstanceQ q(Bind $m)
  let inst2 ← synthInstanceQ q(MonadLiftT MetaM $m)
  have synthed : Q(Expr) := (← quoteExpr (← instantiateMVars pat) s)
  let alt : Q($m $γ) := alt
  makeMatchCode q($inst2) inst oldPatVarDecls argLvlExpr argTyExpr synthed q($e') alt expectedType fun expectedType =>
    return Quoted.unsafeMk (← elabTerm body expectedType)

scoped syntax "_qq_match" term " := " term " | " doSeq : term
macro_rules
  | `(assert! (_qq_match $pat := $e | $alt); $x) => `(_qq_match $pat ← $e | (do $alt) in $x)

partial def isIrrefutablePattern : Term → Bool
  | `(($stx)) => isIrrefutablePattern stx
  | `(⟨$args,*⟩) => args.getElems.all isIrrefutablePattern
  | `(($a, $b)) => isIrrefutablePattern a && isIrrefutablePattern b
  | `(_) => true
  | `(true) => false | `(false) => false -- TODO properly
  | stx => stx.1.isIdent

scoped elab "_comefrom" n:ident "do" b:doSeq " in " body:term : term <= expectedType => do
  let _ ← extractBind expectedType
  let ty ← exprToSyntax expectedType
  elabTerm (← `(have $n:ident : $ty := (do $b:doSeq); $body)) expectedType

scoped syntax "_comefrom" ident "do" doSeq : term
macro_rules | `(assert! (_comefrom $n do $b); $body) => `(_comefrom $n do $b in $body)

scoped macro "comefrom" n:ident "do" b:doSeq : doElem =>
  `(doElem| assert! (_comefrom $n do $b))

def mkLetDoSeqItem [Monad m] [MonadQuotation m] (pat : Term) (rhs : TSyntax `term) (alt : TSyntax ``doSeq) : m (List (TSyntax ``doSeqItem)) := do
  match pat with
    | `(_) => return []
    | _ =>
      if isIrrefutablePattern pat then
        return [← `(doSeqItem| let $pat:term := $rhs)]
      else
        return [← `(doSeqItem| let $pat:term := $rhs | $alt)]

end Impl

section

open Impl

/--
`Qq`s expression matching in `MetaM`, up to reducible defeq.

This syntax is valid in `match`, `let`, and `if let`, but not `fun`.

The usage is very similar to the builtin `Syntax`-matching that uses `` `(<pattern>)`` notation.
As an example, consider matching against a `n : Q(ℕ)`, which can be written

* With a `match` expression,
  ```
  match n with
  | ~q(Nat.gcd $x $y) => handleGcd x y
  | ~q($x + $y) => handleAdd x y
  | _ => throwError "no match"
  ```
* With a `let` expression (if there is a single match)
  ```
  let ~q(Nat.gcd $x $y) := n | throwError "no match"
  handleGcd x y
  ```
* With an `if let` statement
  ```
  if let ~q(Nat.gcd $x $y) := n then
    handleGcd x y
  else if let ~q($x + $y) := n then
    handleAdd x y
  else
    throwError "no match"
  ```

In addition to the obvious `x` and `y` captures,
in the example above `~q` also inserts into the context a term of type `$n =Q Nat.gcd $x $y`.
-/
scoped syntax (name := matcher) "~q(" term ")" : term

partial def Impl.hasQMatch : Syntax → Bool
  | `(~q($_)) => true
  | stx => stx.getArgs.any hasQMatch

partial def Impl.floatQMatch (alt : TSyntax ``doSeq) : Term → StateT (List (TSyntax ``doSeqItem)) MacroM Term
  | `(~q($term)) =>
    withFreshMacroScope do
      let auxDoElem ← `(doSeqItem| let ~q($term) := x | $alt)
      modify fun s => s ++ [auxDoElem]
      `(x)
  | stx => do match stx with
    | ⟨.node i k args⟩ => return ⟨.node i k (← args.mapM (floatQMatch alt ⟨·⟩))⟩
    | stx => return stx

private def push (i : TSyntax ``doSeqItem) : StateT (Array (TSyntax ``doSeqItem)) MacroM Unit :=
  modify fun s => s.push i

partial def unpackParensIdent : Syntax → Option Syntax
  | `(($stx)) => unpackParensIdent stx
  | stx => if stx.isIdent then some stx else none

private partial def floatLevelAntiquot (stx : Syntax.Level) : StateT (Array (TSyntax ``doSeqItem)) MacroM Syntax.Level :=
  if stx.1.isAntiquot && !stx.1.isEscapedAntiquot then
    if !stx.1.getAntiquotTerm.isIdent then
      withFreshMacroScope do
        push <| ← `(doSeqItem| let u : Level := $(⟨stx.1.getAntiquotTerm⟩))
        `(level| u)
    else
      pure stx
  else
    match stx with
    | ⟨.node i k args⟩ => return ⟨Syntax.node i k (← args.mapM (floatLevelAntiquot ⟨·⟩))⟩
    | stx => return stx

private partial def floatExprAntiquot (depth : Nat) : Term → StateT (Array (TSyntax ``doSeqItem)) MacroM Term
  | `(Q($x)) => do `(Q($(← floatExprAntiquot (depth + 1) x)))
  | `(q($x)) => do `(q($(← floatExprAntiquot (depth + 1) x)))
  | `(Type $term) => do `(Type $(← floatLevelAntiquot term))
  | `(Sort $term) => do `(Sort $(← floatLevelAntiquot term))
  | stx => do
    if stx.1.isAntiquot && !stx.1.isEscapedAntiquot then
      let term : Term := ⟨stx.1.getAntiquotTerm⟩
      if term.1.isIdent then
        return stx
      else if depth > 0 then
        return ⟨.mkAntiquotNode stx.1.antiquotKind?.get!.1 (← floatExprAntiquot (depth - 1) term)⟩
      else
        match unpackParensIdent stx.1.getAntiquotTerm with
          | some id =>
            if id.getId.isAtomic then
              return ⟨addSyntaxDollar id⟩
          | none => pure ()
        withFreshMacroScope do
          push <| ← `(doSeqItem| let a : Quoted _ := $term)
          return ⟨addSyntaxDollar (← `(a))⟩
    else
      match stx with
      | ⟨.node i k args⟩ => return ⟨.node i k (← args.mapM (floatExprAntiquot depth ⟨·⟩))⟩
      | stx => return stx

macro_rules
  | `(doElem| let $pat:term := $_) => do
    if !hasQMatch pat then Macro.throwUnsupported
    Macro.throwError "let-bindings with ~q(.) require an explicit alternative"

  | `(doElem| let $pat:term := $rhs:term | $alt:doSeq) => do
    if !hasQMatch pat then Macro.throwUnsupported
    match pat with
      | `(~q($pat)) =>
        let (pat, lifts) ← floatExprAntiquot 0 pat #[]
        let t ← `(doSeqItem| do assert! (_qq_match $pat := $rhs | $alt))
        `(doElem| do $(lifts.push t):doSeqItem*)

      | _ =>
        let (pat', auxs) ← floatQMatch (← `(doSeq| alt)) pat []
        let items :=
          #[← `(doSeqItem| comefrom alt do $alt:doSeq)] ++
          (← mkLetDoSeqItem pat' rhs alt) ++
          auxs
        `(doElem| do $items:doSeqItem*)

  | `(match $[$gen:generalizingParam]? $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    if !patss.any (·.any (hasQMatch ·)) then Macro.throwUnsupported
    `(do match $[$gen]? $[$discrs:term],* with $[| $[$patss:term],* => $rhss:term]*)

  | `(doElem| match $[$gen:generalizingParam]? $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    if !patss.any (·.any (hasQMatch ·)) then Macro.throwUnsupported

    -- only `generalizing := true` (the default) is supported
    if let some stx := gen then
      match stx with
      | `(generalizingParam| (generalizing := true)) => pure ()
      | _ => Macro.throwErrorAt stx "not supported in ~q matching"

    let mut items := #[]
    items := items.push (← `(doSeqItem| comefrom alt do throwError "nonexhaustive match"))
    for pats in patss.reverse, rhs in rhss.reverse do
      let mut subItems : Array (TSyntax ``doSeqItem) := #[]
      for discr in discrs, pat in pats do
        subItems := subItems ++ (← mkLetDoSeqItem pat discr (← `(doSeq| alt)))
      subItems := subItems.push (← `(doSeqItem| do $rhs))
      items := items.push (← `(doSeqItem| comefrom alt do $subItems:doSeqItem*))
    items := items.push (← `(doSeqItem| alt))
    `(doElem| (do $items:doSeqItem*))

end
