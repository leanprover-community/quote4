import Qq.MetaM

namespace Qq

namespace Impl
open Lean Meta Elab Term

def isRedundantLocalInst? (inst : FVarId) : MetaM (Option Expr) := do
  let ldecl ← inst.getDecl
  if ldecl.hasValue then return none
  let rest := (← getLocalInstances).filter (·.fvar != .fvar inst)
  withLCtx (← getLCtx) rest do
  synthInstance? ldecl.type

def findRedundantLocalInst? : MetaM (Option (FVarId × Expr)) := do
  for {fvar, ..} in ← getLocalInstances do
    if let some result ← isRedundantLocalInst? fvar.fvarId! then
      return (fvar.fvarId!, result)
  return none

def findRedundantLocalInstQuoted? :
    MetaM (Option (FVarId × (u : Q(Level)) × (ty : Q(QQ (mkSort $u))) × Q(QQ $ty) × Q(QQ $ty))) := do
  StateT.run' (m := MetaM) (s := {}) do
  unquoteLCtx
  (← withLCtx (← get).unquoted (← determineLocalInstances (← get).unquoted) do
    (← findRedundantLocalInst?).mapM fun (fvar, inst) => do
      let ty ← inferType (.fvar fvar)
      return (← getLevel ty, ty, fvar, inst)) |>.mapM fun (u, ty, fvar, inst) => do
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

scoped syntax "assumeInstancesCommuteImpl" term : term
elab_rules : term <= expectedType | `(assumeInstancesCommuteImpl $cont) => do
  match ← findRedundantLocalInstQuoted? with
  | some ⟨fvar, _, _, lhs, rhs⟩ =>
    let n ← mkFreshUserName ((← fvar.getUserName).eraseMacroScopes.appendAfter "_eq")
    let ty := q(QE $lhs $rhs)
    elabTerm (← `(
        have $(mkIdent n) : $(← exprToSyntax ty) := ⟨⟩
        assumeInstancesCommuteImpl $cont))
      expectedType
  | none => elabTerm cont expectedType

scoped syntax "assertInstancesCommuteDummy" : term
macro_rules
  | `(assert! assertInstancesCommuteDummy; $cont) =>
    `(assertInstancesCommuteImpl $cont)

scoped syntax "assumeInstancesCommuteDummy" : term
macro_rules
  | `(assert! assumeInstancesCommuteDummy; $cont) =>
    `(assumeInstancesCommuteImpl $cont)

end Impl
open Impl

scoped macro "assertInstancesCommute" : doElem =>
  `(doElem| assert! assertInstancesCommuteDummy)

scoped macro "assumeInstancesCommute" : doElem =>
  `(doElem| assert! assumeInstancesCommuteDummy)
