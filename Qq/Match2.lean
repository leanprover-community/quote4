import Qq.Macro
import Qq.MetaM
import Qq.ForLean.Do
import Qq.SortLocalDecls
import Qq.Delab

namespace Qq
open Lean Meta

namespace Impl.Match

inductive Instr
  | whnfR (arg : Nat) (res : Nat)
  | constApp (arg : Nat) (n : Name) (lvls : List Nat) (args : List Nat)
  | levelDec (arg : Nat) (res : Nat)
  | checkDefEq (arg : Nat) (e : Expr)
  | checkDefEqInst (arg : Nat) (e : Expr)
  | checkDefEqR (arg : Nat) (e : Expr)
  deriving Repr, Nonempty, BEq

-- @[match_pattern] def ref (idx : Nat) : Expr := .fvar ⟨.num .anonymous idx⟩
-- @[match_pattern] def refL (idx : Nat) : Level := .param (.num .anonymous idx)

structure CompileState where
  varMVars : Array (Sum Expr Level) := #[]
  instrs : Array Instr := #[]
  constrs : Array Instr := #[]
  deriving Repr

abbrev CompileM := StateT CompileState MetaM

def CompileM.run (k : CompileM α) : MetaM α :=
  StateT.run' k {}

def nextVar (ty : Expr) : CompileM Nat := do
  let i := (← get).varMVars.size
  let mvar ← mkFreshExprMVar ty
  modify fun s => { s with varMVars := s.varMVars.push (.inl mvar) }
  return i

def nextVarL : CompileM Nat := do
  let i := (← get).varMVars.size
  let mvar ← mkFreshLevelMVar
  modify fun s => { s with varMVars := s.varMVars.push (.inr mvar) }
  return i

def ref (idx : Nat) : CompileM Expr := do
  if let some (.inl mvar) := (← get).varMVars[idx]? then
    return mvar
  else
    throwError "invalid index {idx}"

def pushInst (inst : Instr) : CompileM Unit :=
  modify fun s => { s with instrs := s.instrs.push inst }

def pushConstr (inst : Instr) : CompileM Unit :=
  modify fun s => { s with constrs := s.constrs.push inst }

def assertDefEq (a b : Expr) : MetaM Unit := do
  unless ← isDefEq a b do
    throwError "{a} is not definitionally equal to{indentExpr b}"

def applyWithMVars (e : Expr) : Nat → MetaM Expr
  | 0 => return e
  | n+1 => do
    let .forallE bn dom _ _ ← whnf (← inferType e) | throwError "not a function{indentExpr e}"
    applyWithMVars (e.app (← mkFreshExprMVar dom (userName := bn))) n

partial def compile (pat : Expr) (known : Expr) (idx : Nat) (whnf := false) : CompileM Unit := do
  let pat ← whnfR pat
  if let .mvar mvarId := pat then if ← mvarId.isAssignable then
    mvarId.assign (← ref idx)
    assertDefEq known (← ref idx)
    return
  if ← withNewMCtxDepth (isDefEq pat known) then
    return
  if let .const c ls := pat.getAppFn then
    if !whnf then
      let idx' ← nextVar (← inferType pat)
      pushInst <| .whnfR idx idx'
      compile pat known idx' (whnf := true)
      return
    let ls' ← ls.mapM fun _ => nextVarL
    let as' ← pat.getAppArgs.mapM fun a => do nextVar (← inferType a)
    pushInst <| .constApp idx c ls' as'.toList
    let known' ← applyWithMVars (← mkConstWithFreshMVarLevels c) as'.size
    -- dbg_trace known'
    assertDefEq known known'
    logInfo m!"{(← instantiateMVars known, ← instantiateMVars pat)}"
    for i in as', p in pat.getAppArgs, k in known'.getAppArgs do
      if (← isClass? (← inferType p)).isSome then 
        pushConstr <| .checkDefEqInst i p
        if ← withNewMCtxDepth do isDefEq (← inferType k) (← inferType p) then
          _ ← isDefEq k p
        pure ()
      else
        dbg_trace p
        compile p k i
    logInfo m!"{(← instantiateMVars known, ← instantiateMVars pat)}"
    return
  if let .fvar _ := pat.getAppFn then
    pushConstr <| .checkDefEqR idx pat
    assertDefEq pat known
    return
  logError m!"unsupported pattern {pat}"
  -- assertDefEq pat known

open Elab Term
elab "demo" pat:term : term => do
  let pat ← elabTerm pat none
  synthesizeSyntheticMVarsNoPostponing
  let pat ← instantiateMVars pat
  let known ← mkFreshExprMVar (← inferType pat)
  CompileM.run do
  let idx ← nextVar (← inferType pat)
  compile pat known idx
  logInfo (Format.line.joinSep <| ((← get).instrs ++ (← get).constrs).toList.map repr)
  -- logInfo _
  return known

variable {α : Type} [Add α]
#check demo _ + _ = (_ : α)
#check demo (_ + _ : Nat)
#check demo (_ + _ : α)
#check demo (@HAdd.hAdd _ _ _ (_) _ _)