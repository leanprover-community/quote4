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

scoped syntax "assertInstancesCommuteImpl " term : term
elab_rules : term <= expectedType | `(assertInstancesCommuteImpl $cont) => do
  let inst? : Option (Name × Expr) ← StateT.run' (m := MetaM) (s := {}) do
    unquoteLCtx
    (← withLCtx (← get).unquoted (← determineLocalInstances (← get).unquoted) do
      (← findRedundantLocalInst?).mapM fun (fvar, inst) => do
        let ty ← inferType (.fvar fvar)
        return (← getLevel ty, ty, fvar, inst)) |>.mapM fun (u, ty, fvar, inst) => do
    let u' : Q(Level) ← quoteLevel u
    let ty : Q(QQ (mkSort $u')) ← quoteExpr ty
    let lhs : Q(QQ $ty) ← quoteExpr (.fvar fvar)
    let rhs : Q(QQ $ty) ← quoteExpr inst
    return (← mkFreshUserName ((← fvar.getUserName).eraseMacroScopes.appendAfter "_eq"),
      q(withNewMCtxDepth do assertDefEqQ $lhs $rhs))
  match inst? with
  | some (n, cmd) =>
    elabTerm (← `($(← exprToSyntax cmd) >>=
        fun __defeqres =>
          have $(mkIdent n) := __defeqres.1
          assertInstancesCommuteImpl $cont))
      expectedType
  | none => elabTerm cont expectedType

scoped syntax "assertInstancesCommuteDummy" : term
macro_rules
  | `(assert! assertInstancesCommuteDummy; $cont) => `(assertInstancesCommuteImpl $cont)

end Impl
open Impl

scoped macro "assertInstancesCommute" : doElem =>
  `(doElem| assert! assertInstancesCommuteDummy)