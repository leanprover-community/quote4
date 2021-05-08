import Lean
open Lean

namespace Quote

structure QQ (α : Expr) where
  quoted : Expr
  deriving BEq, Hashable

instance : ToString (QQ α) where
  toString q := toString q.quoted

instance : Coe (QQ α) Expr where
  coe := QQ.quoted

open Meta in
protected def QQ.check (e : QQ α) : MetaM Unit := do
  let α' ← inferType e
  unless ← isDefEq α α' do
    throwError "type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg α' α}"
