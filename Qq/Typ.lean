import Lean
open Lean

set_option linter.unusedVariables false

namespace Qq

def QQ (α : Expr) := Expr

protected def QQ.qq (e : Expr) : QQ α := e

instance : BEq (QQ α) := inferInstanceAs (BEq Expr)
instance : Hashable (QQ α) := inferInstanceAs (Hashable Expr)
instance : Inhabited (QQ α) := inferInstanceAs (Inhabited Expr)
instance : ToString (QQ α) := inferInstanceAs (ToString Expr)

instance : Coe (QQ α) Expr where coe e := e
instance : Coe (QQ α) MessageData where coe := .ofExpr
instance : ToMessageData (QQ α) where toMessageData := .ofExpr

protected opaque QQ.qq' {α : Expr} (t : Expr) : QQ α := t

protected abbrev QQ.ty (t : QQ α) : Expr := α

open Meta in
protected def QQ.check (e : QQ α) : MetaM Unit := do
  let α' ← inferType e
  unless ← isDefEq α α' do
    throwError "type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg α' α}"
