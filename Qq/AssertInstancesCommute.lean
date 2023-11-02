import Qq.MetaM

namespace Qq

scoped syntax "assumeInstancesCommute'" term : term

namespace Impl
open Lean Meta Elab Term

def isRedundantLocalInst? (inst : FVarId) : MetaM (Option Expr) := do
  let ldecl ← inst.getDecl
  if ldecl.hasValue then return none
  let rest := (← getLocalInstances).filter (·.fvar != .fvar inst)
  withLCtx (← getLCtx) rest do
  let some inst ← synthInstance? ldecl.type | return none
  return if (← makeDefEq ldecl.toExpr inst).isSome then inst else none

def findRedundantLocalInst? : QuoteM (Option (FVarId × Expr)) := do
  for {fvar, ..} in ← withUnquotedLCtx getLocalInstances do
    if let some (.quoted (.fvar quotedFVar)) := (← read).exprBackSubst.find? fvar then
      if (← quotedFVar.getDecl).hasValue then continue
      if let some result ← withUnquotedLCtx do isRedundantLocalInst? fvar.fvarId! then
        return (fvar.fvarId!, result)
  return none

def findRedundantLocalInstQuoted? :
    TermElabM (Option (FVarId × (u : Q(Level)) × (ty : Q(Quoted (.sort $u))) × Q(Quoted $ty) × Q(Quoted $ty))) := do
  for ldecl in ← getLCtx do
    let ty ← whnfR ldecl.type
    if ty.isMVar then tryPostpone
    if ty.isAppOf ``Quoted then
      if (← instantiateMVars ty.appArg!).hasExprMVar then
        tryPostpone
  StateT.run' (m := MetaM) (s := { mayPostpone := (← read).mayPostpone }) do
  unquoteLCtx
  (← findRedundantLocalInst?).mapM fun (fvar, inst) => do
  let ty ← withUnquotedLCtx do inferType (.fvar fvar)
  let u ← withUnquotedLCtx do getLevel ty
  return ⟨fvar, ← quoteLevel u, ← quoteExpr ty, ← quoteExpr (.fvar fvar), ← quoteExpr inst⟩

scoped syntax "assertInstancesCommuteImpl" term : term
elab_rules : term <= expectedType | `(assertInstancesCommuteImpl $cont) => do
  match ← findRedundantLocalInstQuoted? with
  | some ⟨fvar, _, _, lhs, rhs⟩ =>
    let n ← mkFreshUserName ((← fvar.getUserName).eraseMacroScopes.appendAfter "_eq")
    let cmd := q(withNewMCtxDepth do withDefault do assertDefEqQ $lhs $rhs)
    elabTerm (← `($(← exprToSyntax cmd) >>=
        fun __defeqres =>
          have $(mkIdent n) := __defeqres.1
          assertInstancesCommuteImpl $cont))
      expectedType
  | none => elabTerm cont expectedType

elab_rules : term <= expectedType | `(assumeInstancesCommute' $cont) => do
  match ← findRedundantLocalInstQuoted? with
  | some ⟨fvar, _, _, lhs, rhs⟩ =>
    let n ← mkFreshUserName ((← fvar.getUserName).eraseMacroScopes.appendAfter "_eq")
    let ty := q(QuotedDefEq $lhs $rhs)
    elabTerm (← `(
        have $(mkIdent n) : $(← exprToSyntax ty) := ⟨⟩
        assumeInstancesCommute' $cont))
      expectedType
  | none => elabTerm cont expectedType

scoped syntax "assertInstancesCommuteDummy" : term
macro_rules
  | `(assert! assertInstancesCommuteDummy; $cont) =>
    `(assertInstancesCommuteImpl $cont)

syntax "assumeInstancesCommuteDummy" : term
macro_rules
  | `(assert! assumeInstancesCommuteDummy; $cont) =>
    `(assumeInstancesCommute' $cont)

end Impl
open Impl

scoped macro "assertInstancesCommute" : doElem =>
  `(doElem| assert! assertInstancesCommuteDummy)

scoped macro "assumeInstancesCommute" : doElem =>
  `(doElem| assert! assumeInstancesCommuteDummy)
