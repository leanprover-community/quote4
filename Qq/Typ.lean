import Lean
open Lean

set_option linter.unusedVariables false

namespace Qq

/--
`Quoted α` is the type of Lean expressions having type `α`.

You should usually write this using the notation `Q($α)`.
-/
def Quoted (α : Expr) := Expr

/--
Creates a quoted expression.  Requires that `e` has type `α`.

You should usually write this using the notation `q($e)`.
-/
protected def Quoted.unsafeMk (e : Expr) : Quoted α := e

instance : BEq (Quoted α) := inferInstanceAs (BEq Expr)
instance : Hashable (Quoted α) := inferInstanceAs (Hashable Expr)
instance : Inhabited (Quoted α) := inferInstanceAs (Inhabited Expr)
instance : ToString (Quoted α) := inferInstanceAs (ToString Expr)
instance : Repr (Quoted α) := inferInstanceAs (Repr Expr)

instance : CoeOut (Quoted α) Expr where coe e := e
instance : CoeOut (Quoted α) MessageData where coe := .ofExpr
instance : ToMessageData (Quoted α) where toMessageData := .ofExpr

/-- Gets the type of a quoted expression.  -/
protected abbrev Quoted.ty (t : Quoted α) : Expr := α

/--
`QuotedDefEq lhs rhs` says that the expressions `lhs` and `rhs` are definitionally equal.

You should usually write this using the notation `$lhs =Q $rhs`.
-/
structure QuotedDefEq {α : Quoted (.sort u)} (lhs rhs : Quoted α) : Prop :=
  unsafeIntro ::

/--
`QuotedLevelDefEq u v` says that the levels `u` and `v` are definitionally equal.

You should usually write this using the notation `$u =QL $v`.
-/
structure QuotedLevelDefEq (u v : Level) : Prop :=
  unsafeIntro ::

open Meta in
protected def Quoted.check (e : Quoted α) : MetaM Unit := do
  let α' ← inferType e
  unless ← isDefEq α α' do
    throwError "type mismatch{indentExpr e}\n{← mkHasTypeButIsExpectedMsg α' α}"

open Meta in
protected def QuotedDefEq.check (e : @QuotedDefEq u α lhs rhs) : MetaM Unit := do
  α.check
  lhs.check
  rhs.check
  unless ← isDefEq lhs rhs do
    throwError "{lhs} and {rhs} are not defeq"

open Meta in
protected def QuotedLevelDefEq.check (e : QuotedLevelDefEq lhs rhs) : MetaM Unit := do
  unless ← isLevelDefEq lhs rhs do
    throwError "{lhs} and {rhs} are not defeq"