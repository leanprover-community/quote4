import Qq
open Qq Lean Elab Meta Tactic

elab "print_conjs" : tactic => do
  for ldecl in ← getLCtx do
    if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
      if let ~q($p ∧ $q) := ty then
        logInfo m!"left = {p}, right = {q}"

/--
info: left = true = true, right = False
-/
#guard_msgs in
example (_ : true ∧ False) : true := by
  print_conjs
  trivial
