import Qq
import Lean.Elab.Command
import Lean.Elab.Frontend
import Lean.Elab.InfoTree.Util

open Qq

/-!
# Regression test for https://github.com/leanprover-community/quote4/issues/98

Highlighting or go-to-definition on a level `variable` must not link it to the
entire body of a quotation in which it is only referenced transitively through
antiquotations. Previously, elaborating `q($a = $a)` below recorded a
`TermInfo` for the level variable `u` whose syntax was the whole quotation
body `$a = $a`, so clicking `u` highlighted the entire body and clicking the
`a` binder produced no highlights at all.

The scenario is elaborated programmatically since `elabCommandTopLevel`
discards the info trees of preceding commands.
-/

open Lean Lean.Elab in
run_cmd do
  let src := "open Qq\nvariable {u : Lean.Level} {α : Q(Type u)} (a : Q($α))\nexample : Q(Prop) := q($a = $a)\n"
  let inputCtx := Parser.mkInputContext src "<QqTest/highlight.lean>"
  let (_, parserState, messages) ← Parser.parseHeader inputCtx
  let commandState := Command.mkState (← getEnv) messages (← getOptions)
  let s ← IO.processCommands inputCtx parserState commandState
  if s.commandState.messages.hasErrors then
    for m in s.commandState.messages.toList do
      logError (← m.toString)
    throwError "quote4#98: test input failed to elaborate"
  let trees := s.commandState.infoState.trees.toArray
  let found ← IO.mkRef #[]
  let bad ← IO.mkRef #[]
  for tree in trees do
    tree.visitM' (postNode := fun _ info _ => do
      if let .ofTermInfo ti := info then
        if let .fvar id := ti.expr then
          if let some decl := info.lctx.find? id then
            if decl.userName == `u then
              -- Levels occurring syntactically in the quotation body (e.g.
              -- `Type u`) are recorded on the whole `Type`/`Sort` node; this
              -- is longstanding behaviour. What must not happen is a
              -- reference to `u` on compound syntax such as the whole
              -- quotation body `a = a` (quote4#98).
              if ti.stx.isIdent ||
                  ti.stx.isOfKind ``Lean.Parser.Term.type ||
                  ti.stx.isOfKind ``Lean.Parser.Term.sort then
                found.modify (·.push ti.stx)
              else
                bad.modify (·.push ti.stx))
  let bad ← bad.get
  unless bad.isEmpty do
    throwError "quote4#98: level variable referenced at non-identifier syntax:\
      {Std.Format.join (bad.map fun s => .line ++ Std.Format.text (toString s)).toList}"
  let found ← found.get
  let ok := found.any fun s =>
    match s with
    | .ident _ _ val _ => val.eraseMacroScopes == Name.mkStr1 "$a"
    | _ => false
  unless ok do
    throwError "quote4#98: level variable is not referenced at the `$a` antiquotation"
