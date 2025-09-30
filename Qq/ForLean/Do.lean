import Lean

/-!
Make `Lean.Elab.Term.extractBind` public.
-/

open Lean Meta

namespace Lean.Elab.Term

def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
  let u ← getDecLevel type
  let id        := Lean.mkConst ``Id [u]
  pure { m := id, returnType := type, expectedType := mkApp id type }

partial def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
  match expectedType? with
  | none => throwError "invalid 'do' notation, expected type is not available"
  | some expectedType =>
    let extractStep? (type : Expr) : MetaM (Option ExtractMonadResult) := do
      match type with
      | .app m returnType =>
        return some { m, returnType, expectedType }
      | _ =>
        return none
    let rec extract? (type : Expr) : MetaM (Option ExtractMonadResult) := do
      match (← extractStep? type) with
      | some r => return r
      | none =>
        let typeNew ← whnfCore type
        if typeNew != type then
          extract? typeNew
        else
          if typeNew.getAppFn.isMVar then throwError "invalid 'do' notation, expected type is not available"
          match (← unfoldDefinition? typeNew) with
          | some typeNew => extract? typeNew
          | none => return none
    match (← extract? expectedType) with
    | some r => return r
    | none   => mkIdBindFor expectedType
