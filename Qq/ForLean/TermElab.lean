import Lean

namespace Lean.Elab.Term

/-- Made public from Lean/Elab/Term.lean -/
def saveContext : TermElabM SavedContext :=
  return {
    macroStack := (← read).macroStack
    declName?  := (← read).declName?
    options    := (← getOptions)
    openDecls  := (← getOpenDecls)
    errToSorry := (← read).errToSorry
  }


open Meta in
def dbgPostponementState : TermElabM Unit := do
  dbg_trace "postponement state:"
  for d in (← get).syntheticMVars do
    dbg_trace s!"{mkMVar d.mvarId} {← inferType (mkMVar d.mvarId)} {d.kind} {d.stx}"

  dbg_trace "mvars: {(← getMCtx).decls.toList.map Prod.fst}"
  dbg_trace "eassg: {(← getMCtx).eAssignment.toList}"
  dbg_trace "dassg: {(← getMCtx).dAssignment.toList.map fun (i, d) => (i, d.val)}"