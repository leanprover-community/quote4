import Lean
open Lean

set_option linter.unusedVariables false

namespace Qq

structure QuotedStruct where private mk ::
  private raw : Expr
deriving BEq, Hashable, Inhabited, Repr

/--
`Quoted α` is the type of Lean expressions having type `α`.

You should usually write this using the notation `Q($α)`.
-/
def Quoted (α : Expr) := QuotedStruct

def Quoted.raw (q : Quoted e) : Expr := QuotedStruct.raw q

/--
You should usually write this using the notation `q($e)`.
-/
protected def Quoted.unsafeMk {α : Expr} (e : Expr) : Quoted α := QuotedStruct.mk e

instance : BEq (Quoted α) := inferInstanceAs (BEq QuotedStruct)
instance : Hashable (Quoted α) := inferInstanceAs (Hashable QuotedStruct)
instance : Inhabited (Quoted α) := inferInstanceAs (Inhabited QuotedStruct)
-- instance : ToString (Quoted α) := inferInstanceAs (ToString QuotedStruct)
instance : Repr (Quoted α) := inferInstanceAs (Repr QuotedStruct)

-- instance : CoeOut (Quoted α) Expr where coe e := e
instance : CoeOut (Quoted α) MessageData where coe e := .ofExpr e.raw
instance : ToMessageData (Quoted α) where toMessageData e := .ofExpr e.raw

/-- Gets the type of a quoted expression.  -/
protected abbrev Quoted.ty (t : Quoted α) : Expr := α

/--
`QuotedDefEq lhs rhs` says that the expressions `lhs` and `rhs` are definitionally equal.

You should usually write this using the notation `$lhs =Q $rhs`.
-/
structure QuotedDefEq {α : Quoted (.sort u)} (lhs rhs : Quoted α.raw) : Prop :=
  unsafeIntro ::

/--
`QuotedLevelDefEq u v` says that the levels `u` and `v` are definitionally equal.

You should usually write this using the notation `$u =QL $v`.
-/
structure QuotedLevelDefEq (u v : Level) : Prop :=
  unsafeIntro ::

open Meta in
protected def Quoted.check (e : Quoted α) : MetaM Unit := do
  let α' ← inferType e.raw
  unless ← isDefEq α α' do
    throwError "type mismatch{indentExpr e.raw}\n{← mkHasTypeButIsExpectedMsg α' α}"

open Meta in
protected def QuotedDefEq.check (e : @QuotedDefEq u α lhs rhs) : MetaM Unit := do
  α.check
  lhs.check
  rhs.check
  unless ← isDefEq lhs.raw rhs.raw do
    throwError "{lhs} and {rhs} are not defeq"

open Meta in
protected def QuotedLevelDefEq.check (e : QuotedLevelDefEq lhs rhs) : MetaM Unit := do
  unless ← isLevelDefEq lhs rhs do
    throwError "{lhs} and {rhs} are not defeq"
