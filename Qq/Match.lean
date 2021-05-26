import Qq.Macro
import Qq.MetaM
import Qq.ForLean.Do

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

def PatVarDecl.fvar (decl : PatVarDecl) : Q(%(decl.fvarTy)) :=
  ⟨mkFVar decl.fvarId⟩

def mkIsDefEqType : List PatVarDecl → Q(Type)
  | [] => q(Bool)
  | decl :: decls => q(%(decl.fvarTy) × %(mkIsDefEqType decls))

def mkIsDefEqResult (val : Bool) : (decls : List PatVarDecl) → Q(%(mkIsDefEqType decls))
  | [] => q(val)
  | decl :: decls => q((%(decl.fvar), %(mkIsDefEqResult val decls)))

def mkIsDefEqResultVal : (decls : List PatVarDecl) → Q(%(mkIsDefEqType decls)) → Q(Bool)
  | [], val => q(val)
  | decl :: decls, val => mkIsDefEqResultVal decls q(val.2)

def mkLambda' (n : Name) (fvar : Expr) (ty : Expr) (body : Expr) : Expr :=
  mkLambda n BinderInfo.default ty (body.abstract #[fvar])

def mkLet' (n : Name) (fvar : Expr) (ty : Expr) (val : Expr) (body : Expr) : Expr :=
  mkLet n ty val (body.abstract #[fvar])

def mkLambdaQ (n : Name) (fvar : QQ α) (body : QQ β) : QQ (mkForall n BinderInfo.default α β) :=
  ⟨mkLambda n BinderInfo.default α (body.quoted.abstract #[fvar])⟩

def mkInstantiateMVars (decls : List PatVarDecl) : List PatVarDecl → Q(MetaM %(mkIsDefEqType decls))
  | [] => q(%(mkIsDefEqResult true decls))
  -- https://github.com/leanprover/lean4/issues/471
  | { ty := none, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := none, fvarId := fvarId, userName := userName }
    q(Bind.bind (instantiateLevelMVars %(decl.fvar))
      %(show Q(Level → MetaM %(mkIsDefEqType decls)) from
        mkLambdaQ _ decl.fvar q(%(mkInstantiateMVars decls rest))))
  | { ty := some ty, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := some ty, fvarId := fvarId, userName := userName }
    q(Bind.bind (instantiateMVars %(decl.fvar))
      %(show Q(Expr → MetaM %(mkIsDefEqType decls)) from
        mkLambdaQ _ decl.fvar q(%(mkInstantiateMVars decls rest))))

def mkIsDefEqCore (decls : List PatVarDecl) (pat discr : Q(Expr)) :
    List PatVarDecl → Q(MetaM %(mkIsDefEqType decls))
  | { ty := none, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := none, fvarId := fvarId, userName := userName }
    q(Bind.bind mkFreshLevelMVar %(mkLambdaQ `x decl.fvar (mkIsDefEqCore decls pat discr rest)))
  | { ty := some ty, fvarId := fvarId, userName := userName } :: rest =>
    let decl : PatVarDecl := { ty := some ty, fvarId := fvarId, userName := userName }
    q(Bind.bind (mkFreshExprMVar ty) %(mkLambdaQ `x decl.fvar (mkIsDefEqCore decls pat discr rest)))
  | [] => q(do
      let matches ← withReducible $ isDefEq pat discr
      if matches then
        %(mkInstantiateMVars decls decls)
      else
        %(mkIsDefEqResult false decls))

def mkIsDefEq (decls : List PatVarDecl) (pat discr : Q(Expr)) : Q(MetaM %(mkIsDefEqType decls)) :=
  q(withNewMCtxDepth %(mkIsDefEqCore decls pat discr decls))

def withLetHave [Monad m] [MonadControlT MetaM m] [MonadLCtx m] {α : Q(Sort u)} {β : Q(Sort v)}
    (fvarId : FVarId) (userName : Name) (val : Q(α)) (k : Q(α) → m Q(β)) : m Q(β) := do
  withExistingLocalDecls [LocalDecl.cdecl (← getLCtx).decls.size fvarId userName α BinderInfo.default] do
    QQ.qq $ ← mkLet' userName (mkFVar fvarId) α val (← k ⟨mkFVar fvarId⟩)

def mkQqLets {γ : Q(Type)} : (decls : List PatVarDecl) → Q(%(mkIsDefEqType decls)) → TermElabM Q(γ) → TermElabM Q(γ)
  | { ty := none, fvarId := fvarId, userName := userName } :: decls, acc, cb =>
    let decl : PatVarDecl := { ty := none, fvarId := fvarId, userName := userName }
    withLetHave fvarId userName (α := q(Level)) q(acc.1) fun fvar => mkQqLets decls q(acc.2) cb
  | { ty := some ty, fvarId := fvarId, userName := userName } :: decls, acc, cb =>
    let decl : PatVarDecl := { ty := some ty, fvarId := fvarId, userName := userName }
    withLetHave fvarId userName (α := q(QQ ty)) q(⟨acc.1⟩) fun fvar => mkQqLets decls q(acc.2) cb
  | [], acc, cb => cb

def replaceTempExprsByQVars : List PatVarDecl → Expr → Expr
  | [], e => e
  | { ty := some ty, fvarId := fvarId, .. } :: decls, e =>
    ((replaceTempExprsByQVars decls e).abstract #[mkFVar fvarId]).instantiate
      #[mkApp2 (mkConst ``QQ.quoted) ty (mkFVar fvarId)]
  | { ty := none, .. } :: decls, e =>
    replaceTempExprsByQVars decls e

def makeMatchCode {γ : Q(Type)} {m : Q(Type → Type v)} [Q(MonadLiftT MetaM m)] [Q(Bind m)]
    (decls : List PatVarDecl) (pat discr : Q(Expr)) (alt : Q(m γ)) (k : TermElabM Q(m γ)) : TermElabM Q(m γ) := do
  let nextDecls : List PatVarDecl :=
    decls.map fun decl => { decl with ty := decl.ty.map fun ⟨e⟩ => ⟨replaceTempExprsByQVars decls e⟩ }
  let next : QQ _ ← withLocalDeclD (← mkFreshBinderName) (mkIsDefEqType decls) fun fv => do
    let fv : Q(%(mkIsDefEqType decls)) := ⟨fv⟩
    let next : Q(m γ) :=
      q(if %(mkIsDefEqResultVal decls fv) then
          %(← mkQqLets nextDecls ⟨fv⟩ k)
        else
          alt)
    show Q(%(mkIsDefEqType decls) → m γ) from
      QQ.qq $ mkLambda' `result fv (mkIsDefEqType decls) next
  pure q(Bind.bind %(mkIsDefEq decls pat discr) next)

/- def unquoteQQMVar (mvar : MVarId) : UnquoteM Expr := do -/
/-   unquoteLCtx -/
/-  -/
/-   let lctx ← getLCtx -/
/-   let mdecl ← (← getMCtx).getDecl mvar -/
/-  -/
/-   let ty ← whnf mdecl.type -/
/-   let ty ← instantiateMVars ty -/
/-   if ty.isAppOf ``QQ then -/
/-     let et := ty.getArg! 0 -/
/-     let newET ← unquoteExpr et -/
/-     let newLCtx := (← get).unquoted -/
/-     let newLocalInsts ← determineLocalInstances newLCtx -/
/-     let exprBackSubst := (← get).exprBackSubst -/
/-     let newMVar ← mkFreshExprMVarAt newLCtx newLocalInsts newET -/
/-     modify fun s => { s with exprSubst := s.exprSubst.insert (mkMVar mvar) newMVar } -/
/-     newMVar -/
/-   else -/
/-     throwError "unsupported type {ty}" -/

partial def getArityOf (n : Name) (pat : Syntax) : Nat := do
  match pat with
    | `($n':ident $args:term*) => do
      if n'.getId == n then
        return args.size
    | _ => ()

  pat.getArgs.foldr (fun s a => do a.max (← getArityOf n s)) 0

def mkNAryFunctionType : Nat → MetaM Expr
  | 0 => mkFreshTypeMVar
  | n+1 => do withLocalDeclD `x (← mkFreshTypeMVar) fun x => do
    mkForallFVars #[x] (← mkNAryFunctionType n)

def makeIntoNAryFunction (n : Expr) (arity : Nat) : MetaM Unit := do
  let ty ← instantiateMVars (← inferType n)
  if ty.isMVar then
    try
      let _ ← isDefEq ty (← mkNAryFunctionType arity)
    catch _ =>
      ()

def setupHoPatVar (n : Expr) (pat : Syntax) : MetaM Unit := do
  let arity := getArityOf (← getLocalDecl n.fvarId!).userName pat
  unless arity == 0 do
    makeIntoNAryFunction n arity


def elabPat (argTyExpr : Expr) (pat : Syntax) : TermElabM (Expr × Array LocalDecl × Array Name) :=
  unquotingLCtx do
    let unquotedArgTy ← unquoteExpr argTyExpr

    withoutAutoBoundImplicit do withAutoBoundImplicit do
        for patVar in (← addAutoBoundImplicits #[]) do setupHoPatVar patVar pat
        let pat ← Lean.Elab.Term.elabTerm pat unquotedArgTy
        let patVars ← addAutoBoundImplicits #[]
        withoutAutoBoundImplicit do
          let pat ← ensureHasType unquotedArgTy pat
          synthesizeSyntheticMVars false
          let pat ← instantiateMVars pat

          let mctx ← getMCtx
          let levelNames ← getLevelNames
          let r := mctx.levelMVarToParam (fun n => levelNames.elem n) pat `u 1
          setMCtx r.mctx

          /- let pat ← instantiateMVars pat -/
          /- assignExprMVar lastId pat -/

          let mut newDecls := #[]
          for newMVar in ← getMVars pat do
            let fvarId ← mkFreshId
            let type ← instantiateMVars (← Meta.getMVarDecl newMVar).type
            let userName ← mkFreshBinderName
            newDecls := newDecls.push $ LocalDecl.cdecl arbitrary fvarId userName type BinderInfo.default
            assignExprMVar newMVar (mkFVar fvarId)

          withExistingLocalDecls newDecls.toList do
            (← instantiateMVars pat,
              ← sortLocalDecls ((← patVars.mapM fun e => do
                 instantiateLocalDeclMVars (← getFVarLocalDecl e)) ++ newDecls),
              r.newParamNames)

-- set_option maxHeartbeats 200000 in
scoped elab "_qq_match" pat:term " ← " e:term " | " alt:term "; " body:term : term <= expectedType => do
  let emr ← extractBind expectedType
  let alt : Expr ← elabTermEnsuringType alt expectedType

  let argTyExpr ← mkFreshExprMVar (mkConst ``Expr)
  let argTyExpr : Q(Expr) := QQ.qq' argTyExpr
  let e'ty : Q(Type) := q(QQ argTyExpr)
  let e' ← elabTermEnsuringTypeQ e q(e'ty)
  let argTyExpr ← instantiateMVars argTyExpr

  let (pat, patVarDecls, newLevels) ← elabPat argTyExpr pat

  /- let mut s := s -/
  let mut oldPatVarDecls : List PatVarDecl := []
  for newLevel in newLevels do
    let fvarId ← mkFreshId
    oldPatVarDecls := oldPatVarDecls ++ [{ ty := none, fvarId := fvarId, userName := newLevel }]
    /- s := { s with levelBackSubst := s.levelBackSubst.insert (mkLevelParam newLevel) (mkFVar fvarId) } -/

  for ldecl in (patVarDecls : Array LocalDecl) do
    let qty ← quoteExpr ldecl.type
    oldPatVarDecls := oldPatVarDecls ++ [{ ty := some ⟨qty⟩, fvarId := ldecl.fvarId, userName := ldecl.userName }]
    /- s := { s with exprBackSubst := s.exprBackSubst.insert ldecl.toExpr ldecl.toExpr } -/

  let m : Q(Type → Type) := QQ.qq' emr.m
  let γ : Q(Type) := QQ.qq' emr.α
  let inst : Q(Bind m) := QQ.qq' emr.hasBindInst
  let inst2 ← synthInstanceQ q(MonadLiftT MetaM m)
  let synthed : Q(Expr) := QQ.qq' (← quoteExpr pat)
  let alt : Q(m γ) := ⟨alt⟩
  QQ.quoted $ ← makeMatchCode (γ := γ) (m := q(m)) oldPatVarDecls synthed q(e') q(alt) do
    QQ.qq (← elabTerm body expectedType)

scoped syntax "_qq_match" term " ← " term " | " doElem : term
macro_rules
  | `(assert! (_qq_match $pat ← $e | $alt); $x) => `(_qq_match $pat ← $e | (do $alt:doElem); $x)

partial def isIrrefutablePattern : Syntax → Bool
  | `(($stx)) => isIrrefutablePattern stx
  | `(⟨$args,*⟩) => args.getElems.all isIrrefutablePattern
  | `(($a, $b)) => isIrrefutablePattern a && isIrrefutablePattern b
  | `(_) => true
  | `(true) => false | `(false) => false -- TODO properly
  | stx => stx.isIdent

scoped elab "_comefrom" n:ident "do" b:doElem ";" body:term : term <= expectedType => do
  let _ ← extractBind expectedType
  assignExprMVar (← elabTerm (← `(?m)) none).mvarId! expectedType
  elabTerm (← `(let $n:ident : ?m := (do $b:doElem); $body)) expectedType

scoped syntax "_comefrom" ident "do" doElem : term
macro_rules | `(assert! (_comefrom $n do $b); $body) => `(_comefrom $n do $b; $body)

scoped macro "comefrom" n:ident "do" b:doElem : doElem =>
  `(doElem| assert! (_comefrom $n do $b))

def mkLetDoSeqItem [Monad m] [MonadQuotation m] (pat rhs alt : Syntax) : m (List Syntax) := do
  match pat with
    | `(_) => []
    | _ =>
      if isIrrefutablePattern pat then
        [← `(doSeqItem| let $pat:term ← $rhs)]
      else
        [← `(doSeqItem| let $pat:term ← $rhs | $alt)]

end Impl

section

open Impl

scoped syntax "~q(" term ")" : term

partial def Impl.hasQMatch : Syntax → Bool
  | `(~q($x)) => true
  | stx => stx.getArgs.any hasQMatch

partial def Impl.floatQMatch (alt : Syntax) : Syntax → StateT (List Syntax) MacroM Syntax
  | `(~q($term)) =>
    withFreshMacroScope do
      let auxDoElem ← `(doSeqItem| let ~q($term) ← x | $alt)
      modify fun s => s ++ [auxDoElem]
      `(x)
  | stx => do match stx with
    | Syntax.node k args => Syntax.node k (← args.mapM (floatQMatch alt))
    | stx => stx

macro_rules
  | `(doElem| let $pat:term ← $rhs) => do
    if !hasQMatch pat then Macro.throwUnsupported
    Macro.throwError "let-bindings with ~q(.) require an explicit alternative"

  | `(doElem| let $pat:term ← $rhs:doElem | $alt:doElem) => do
    if !hasQMatch pat then Macro.throwUnsupported
    match pat with
      | `(~q($pat)) => `(doElem| do let rhs ← $rhs; assert! (_qq_match $pat ← rhs | $alt))
      | _ =>
        let (pat', auxs) ← floatQMatch (← `(doElem| alt)) pat []
        let items :=
          #[← `(doSeqItem| comefrom alt do $alt:doElem)] ++
          (← mkLetDoSeqItem pat' rhs alt) ++
          auxs
        `(doElem| do $items:doSeqItem*)

  | `(match $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    if !patss.any (·.any hasQMatch) then Macro.throwUnsupported
    `(do match $[$discrs:term],* with $[| $[$patss:term],* => $rhss:term]*)

  | `(doElem| match $[$discrs:term],* with $[| $[$patss],* => $rhss]*) => do
    if !patss.any (·.any hasQMatch) then Macro.throwUnsupported
    let discrs ← discrs.mapM fun d => withFreshMacroScope do
      (← `(x), ← `(doSeqItem| let x := $d:term))
    let mut items := discrs.map (·.2)
    let discrs := discrs.map (·.1)
    items := items.push (← `(doSeqItem| comefrom alt do throwError "nonexhaustive match"))
    for pats in patss.reverse, rhs in rhss.reverse do
      let mut subItems : Array Syntax := #[]
      for discr in discrs, pat in pats do
        subItems := subItems ++ (← mkLetDoSeqItem pat (← `(doElem| $discr:term)) (← `(doElem| alt)))
      subItems := subItems.push (← `(doSeqItem| do $rhs))
      items := items.push (← `(doSeqItem| comefrom alt do do $subItems:doSeqItem*))
    items := items.push (← `(doSeqItem| alt))
    `(doElem| (do $items:doSeqItem*))

end
