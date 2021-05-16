import Lean
open Lean Meta

instance : ToString LocalDecl where
  toString ldecl :=
    if ldecl.isLet then
      s!"{ldecl.userName} : {ldecl.type} := {ldecl.value}"
    else
      s!"{ldecl.userName} : {ldecl.type}"

instance : ToString LocalContext where
  toString lctx := String.join $ List.join $ lctx.decls.toList.map fun ldecl =>
    match ldecl with | none => [] | some ldecl => [toString ldecl, "\n"]

def instantiateLCtxMVars (lctx : LocalContext) : MetaM LocalContext := do
  let mut lctx' : LocalContext := {}
  for ldecl in lctx do
    lctx' := lctx'.addDecl (← instantiateLocalDeclMVars ldecl)
  lctx'