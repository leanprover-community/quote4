import Qq.Macro
open Qq Lean Elab PrettyPrinter.Delaborator Meta Impl Std

namespace Qq

namespace Impl

-- HACK: https://github.com/leanprover/lean4/issues/494
scoped syntax "q(" term ")​" : term
scoped syntax "Q(" term ")​" : term

-- TODO: this probably exists in the library
private def failureOnError (x : MetaM α) : DelabM α := do
  let y : MetaM (Option α) := do try some (← x) catch _ => none
  match ← y with
    | some a => a
    | none => failure

private def unquote (e : Expr) : UnquoteM (Expr × LocalContext) := do
  unquoteLCtx (gadgets := false)
  let newE ← unquoteExpr e
  (newE, (← get).unquoted)

def delabQuoted : Delab := do
  let e ← getExpr
  let ((newE, newLCtx), _) ← failureOnError $ (unquote e).run {}
  withLCtx newLCtx (← determineLocalInstances newLCtx) do
    withReader (fun cfg => { cfg with expr := newE }) delab

@[delab app.Qq.QQ]
def delabQ : Delab := do
  guard $ (← getExpr).getAppNumArgs == 1
  let stx ← withAppArg delabQuoted
  `(Q($stx)​)

@[delab app.Qq.QQ.qq]
def delabq : Delab := do
  guard $ (← getExpr).getAppNumArgs == 2
  let stx ← withAppArg delabQuoted
  `(q($stx)​)
