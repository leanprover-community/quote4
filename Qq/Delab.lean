import Qq.Macro
open Qq Lean Elab PrettyPrinter.Delaborator SubExpr Meta Impl Std

namespace Qq

namespace Impl

register_option pp.qq : Bool := {
  defValue := true
  group    := "pp"
  descr    := "(pretty printer) print quotations as q(...) and Q(...)"
}

-- TODO: this probably exists in the library
private def failureOnError (x : MetaM α) : DelabM α := do
  let y : MetaM (Option α) := do try return some (← x) catch _ => return none
  match ← y with
    | some a => return a
    | none => failure

private def unquote (e : Expr) : UnquoteM (Expr × LocalContext) := do
  unquoteLCtx
  let newE ← unquoteExpr e
  return (newE, (← get).unquoted)

def checkQqDelabOptions : DelabM Unit := do
  unless ← getPPOption (·.getBool `pp.qq true) do failure
  if ← getPPOption getPPExplicit then failure

instance : MonadLift UnquoteM (StateT UnquoteState DelabM) where
  monadLift k s := k s

def delabQuoted : StateT UnquoteState DelabM Term := do
  let e ← getExpr
  -- `(failure : DelabM _)` is of course completely different than `(failure : MetaM _)`...
  let some newE ← (try some <$> unquoteExpr e catch _ => failure : UnquoteM _) | failure
  let newLCtx := (← get).unquoted
  withLCtx newLCtx (← determineLocalInstances newLCtx) do
    withTheReader SubExpr (fun s => { s with expr := newE }) delab

def withDelabQuoted (k : StateT UnquoteState DelabM Term) : Delab :=
  withIncRecDepth do
  StateT.run' (s := { mayPostpone := false }) <|
  show StateT UnquoteState DelabM Term from do
  unquoteLCtx
  let mut res ← k
  let showNested := `pp.qq._nested
  if (← getOptions).get showNested true then
    for fv in (← get).abstractedFVars.reverse do
      if let some (.quoted expr) := (← get).exprBackSubst.find? (.fvar fv) then
      if let some decl := (← get).unquoted.find? fv then
      if (res.1.find? (·.getId == decl.userName)).isSome then
      if let some name := removeDollar decl.userName then
      let pos ← nextExtraPos
      res ← withTheReader SubExpr (fun _ => { expr, pos }) do
      withOptions (·.set showNested false) do
      `(let $(mkIdent name) := $(← delab); $res)
  return res

def delabQuotedLevel : DelabM Syntax.Level := do
  let e ← getExpr
  let (newE, _) ← failureOnError do
    StateT.run (s := { mayPostpone := false }) do
      unquoteLevelLCtx (addDefEqs := false)
      unquoteLevel e
  return newE.quote max_prec

@[delab app.Qq.Quoted]
def delabQ : Delab := do
  guard $ (← getExpr).getAppNumArgs == 1
  checkQqDelabOptions
  withDelabQuoted do
  let stx ← withAppArg delabQuoted
  `(Q($stx))

@[delab app.Qq.Quoted.unsafeMk]
def delabq : Delab := do
  guard $ (← getExpr).getAppNumArgs == 2
  checkQqDelabOptions
  withDelabQuoted do
  let stx ← withAppArg delabQuoted
  `(q($stx))

@[delab app.Qq.QuotedDefEq]
def delabQuotedDefEq : Delab := do
  guard $ (← getExpr).getAppNumArgs == 4
  checkQqDelabOptions
  withDelabQuoted do
  let lhs ← withAppFn do withAppArg delabQuoted
  let rhs ← withAppArg delabQuoted
  `($lhs =Q $rhs)

@[delab app.Qq.QuotedLevelDefEq]
def delabQuotedLevelDefEq : Delab := do
  guard $ (← getExpr).getAppNumArgs == 2
  checkQqDelabOptions
  let lhs ← withAppFn do withAppArg delabQuotedLevel
  let rhs ← withAppArg delabQuotedLevel
  `($lhs:level =QL $rhs:level)
