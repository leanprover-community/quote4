import Lean

namespace Std.PersistentHashMap

def toArray [BEq α] [Hashable α] (m : PersistentHashMap α β) : Array (α × β) :=
  m.foldl (init := #[]) fun ps k v => ps.push (k, v)

end Std.PersistentHashMap

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

  let mctx ← getMCtx
  dbg_trace "mvars:"
  for (mvarid, _) in mctx.decls.toArray do
    dbg_trace "  {mvarid}"
  dbg_trace "eassg:"
  for (mvarid, eassg) in mctx.eAssignment.toArray do
    dbg_trace "  {mvarid} -> {eassg}"
  dbg_trace "dassg:"
  for (mvarid, dassg) in mctx.dAssignment.toArray do
    dbg_trace "  {mvarid} ->[{dassg.fvars.size}] {dassg.val}"
  dbg_trace "lassg:"
  for (mvarid, lassg) in mctx.lAssignment.toArray do
    dbg_trace "  {mvarid} -> {lassg}"