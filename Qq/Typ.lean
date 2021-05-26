import Lean
open Lean

namespace Qq

structure QQ (α : Expr) where qq ::
  quoted : Expr
  deriving BEq, Hashable, Inhabited

unif_hint (q : QQ t) (e : Expr) where
  q =?= QQ.qq e ⊢ q.quoted =?= e

attribute [class] QQ

protected constant QQ.qq' {α : Expr} (t : Expr) : QQ α := ⟨t⟩

protected abbrev QQ.ty (t : QQ α) : Expr := α

instance : ToString (QQ α) where
  toString q := toString q.quoted

instance : Coe (QQ α) Expr where
  coe := QQ.quoted

open Meta in
protected def QQ.check (e : QQ α) : MetaM Unit := do
  let α' ← inferType e
  unless ← isDefEq α α' do
    throwError "type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg α' α}"
