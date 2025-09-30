/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Basic

open Lean Meta

namespace Qq

namespace SortLocalDecls

structure Context where
  localDecls : NameMap LocalDecl := {}

structure State where
  visited : NameSet := {}
  result  : Array LocalDecl := #[]

abbrev M := ReaderT Context $ StateRefT State MetaM

mutual
  partial def visitExpr (e : Expr) : M Unit := do
    match e with
    | .proj _ _ e    => visitExpr e
    | .forallE _ d b _ => visitExpr d; visitExpr b
    | .lam _ d b _     => visitExpr d; visitExpr b
    | .letE _ t v b _  => visitExpr t; visitExpr v; visitExpr b
    | .app f a       => visitExpr f; visitExpr a
    | .mdata _ b     => visitExpr b
    | .mvar _        => let v ← instantiateMVars e; unless v.isMVar do visitExpr v
    | .fvar fvarId   => if let some localDecl := (← read).localDecls.find? fvarId.name then visitLocalDecl localDecl
    | _              => return ()

  partial def visitLocalDecl (localDecl : LocalDecl) : M Unit := do
    unless (← get).visited.contains localDecl.fvarId.name do
      modify fun s => { s with visited := s.visited.insert localDecl.fvarId.name }
      visitExpr localDecl.type
      if let some val := localDecl.value? then
        visitExpr val
      modify fun s => { s with result := s.result.push localDecl }
end

end SortLocalDecls

open SortLocalDecls in
def sortLocalDecls (localDecls : Array LocalDecl) : MetaM (Array LocalDecl) :=
  let aux : M (Array LocalDecl) := do localDecls.forM visitLocalDecl; return (← get).result
  aux.run { localDecls := localDecls.foldl (init := {}) fun s d => s.insert d.fvarId.name d } |>.run' {}
