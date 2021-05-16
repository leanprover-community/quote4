import Lean
open Lean Elab PrettyPrinter Delaborator Meta

namespace Lean

private def quoteName : Name → Syntax
  | Name.anonymous => mkCIdent ``Name.anonymous
  | name => Syntax.node ``Lean.Parser.Term.quotedName
      #[Syntax.node `nameLit #[Syntax.atom SourceInfo.none (toString (repr name))]]

-- instance : Quote Name := ⟨quoteName⟩

def delabName : Delab := do
  let e ← getExpr
  let some n ← (show MetaM (Option Name) from do
    try some (← reduceEval e) catch _ => none) | failure
  pure (quoteName n)

@[delab app.Lean.Name.mkStr] def delabNameMkStr : Delab := delabName
@[delab app.Lean.Name.mkNum] def delabNameMkNum : Delab := delabName
