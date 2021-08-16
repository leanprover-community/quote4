import Lean

/-!
Make `Lean.Elab.Term.extractBind` public.
-/

open Lean Meta

namespace Lean.Elab.Term

def mkIdBindFor (type : Expr) : TermElabM ExtractMonadResult := do
  let u ← getDecLevel type
  let id        := Lean.mkConst ``Id [u]
  let idBindVal := Lean.mkConst ``Id.hasBind [u]
  pure { m := id, hasBindInst := idBindVal, α := type, expectedType := mkApp id type, isPure := true }

partial def extractBind (expectedType? : Option Expr) : TermElabM ExtractMonadResult := do
  match expectedType? with
  | none => throwError "invalid 'do' notation, expected type is not available"
  | some expectedType =>
    let extractStep? (type : Expr) : MetaM (Option ExtractMonadResult) := do
      match type with
      | Expr.app m α _ =>
        try
          let bindInstType ← mkAppM ``Bind #[m]
          let bindInstVal  ← Meta.synthInstance bindInstType
          return some { m := m, hasBindInst := bindInstVal, α := α, expectedType := expectedType, isPure := false }
        catch _ =>
          return none
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
