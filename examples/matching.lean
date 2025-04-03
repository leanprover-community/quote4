import Qq
open Qq Lean

partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) :
    Q($α) → MetaM (List Q($α))
  | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
  | n => return [n]

opaque k : Nat
opaque m : Nat

abbrev double (a : Nat) := a + a

#eval summands q(inferInstance) q(double k + m)

#eval show MetaM Bool from do
  let x : Q(Nat) := q(k + m)
  match x with
  | ~q(Nat.add $a $b) => return true
  | _ => return false

abbrev square (a : Nat) :=
  have : Add Nat := ⟨(· * ·)⟩
  a + a

#eval square 10
#eval summands q(inferInstance) q(k + square (square k))
#eval summands q(⟨(· * ·)⟩) q(k * square (square k))

set_option pp.macroStack true in
def matchProd (e : Nat × Q(Nat)) : MetaM Bool := do
  let (2, ~q(1)) := e | return false
  return true

#eval do guard <| (←matchProd (2, q(1))) == true
#eval do guard <| (←matchProd (1, q(1))) == false
#eval do guard <| (←matchProd (2, q(2))) == false

def matchNatSigma (e : (n : Q(Type)) × Q($n)) : MetaM (Option Q(Nat)) := do
  let ⟨~q(Nat), ~q($n)⟩ := e | return none
  return some n

#eval do guard <| (← matchNatSigma ⟨q(Nat), q(1)⟩) == some q(1)
#eval do guard <| (← matchNatSigma ⟨q(Nat), q(2)⟩) == some q(2)
#eval do guard <| (← matchNatSigma ⟨q(Int), q(2)⟩) == none


/-- Given `x + y` of Nat, returns `(x, y)`. Otherwise fail. -/
def getNatAdd (e : Expr) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  let ⟨Level.succ Level.zero, ~q(Nat), ~q($a + $b)⟩ ← inferTypeQ e | return none
  return some (a, b)

#eval do guard <| (← getNatAdd q(1 + 2)) == some (q(1), q(2))
#eval do guard <| (← getNatAdd q((1 + 2 : Int))) == none


-- tests for gh-21
section test_return

def foo_let1 (T : Q(Type)) : MetaM Nat := do
  let x ← do
    let ~q(Prop) := T | pure (1 : Nat)
    return (2 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_let1 q(Prop)) == 2
#eval do guard <| (←foo_let1 q(Nat)) == 3 + 1

def foo_let2 (T : Q(Type)) : MetaM Nat := do
  let x ← do
    let ~q(Prop) := T | return (1 : Nat)
    pure (2 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_let2 q(Prop)) == 3 + 2
#eval do guard <| (←foo_let2 q(Nat)) == 1


def foo_match1 (T : Q(Type)) : MetaM Nat := do
  let x : Nat ← match T with
    | ~q(Prop) => return (2 : Nat)
    | _ => pure (1 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_match1 q(Prop)) == 2
#eval do guard <| (←foo_match1 q(Nat)) == 3 + 1

def foo_match2 (T : Q(Type)) : MetaM Nat := do
  let x : Nat ← match T with
    | ~q(Prop) => pure (2 : Nat)
    | _ => return (1 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_match2 q(Prop)) == 3 + 2
#eval do guard <| (←foo_match2 q(Nat)) == 1

def foo_if_let1 (T : Q(Type)) : MetaM Nat := do
  let x : Nat ←
    if let ~q(Prop) := T then
      return (2 : Nat)
    else
      pure (1 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_if_let1 q(Prop)) == 2
#eval do guard <| (←foo_if_let1 q(Nat)) == 3 + 1

def foo_if_let2 (T : Q(Type)) : MetaM Nat := do
  let x : Nat ←
    if let ~q(Prop) := T then
      pure (2 : Nat)
    else
      return (1 : Nat)
  pure (3 + x)

#eval do guard <| (←foo_if_let2 q(Prop)) == 3 + 2
#eval do guard <| (←foo_if_let2 q(Nat)) == 1

end test_return
def pairLit (u : Lean.Level) (α : Q(Type u)) (a : Q($α)) : MetaM Q($α × $α) := do
  match u, α, a with
  | 0, ~q(Nat), n => return q(($n, $n))
  | 0, ~q(Int), z => return q(($z, $z))
  | _, _, _ => failure

#eval show MetaM Unit from do guard <| (←pairLit _ _ q(2)) == q((2, 2))

-- `generalizing := true` is a no-op
def pairLit' (u : Lean.Level) (α : Q(Type u)) (a : Q($α)) : MetaM Q($α × $α) := do
  match (generalizing := true) u, α, a with
  | 0, ~q(Nat), n => return q(($n, $n))
  | 0, ~q(Int), z => return q(($z, $z))
  | _, _, _ => failure

#eval show MetaM Unit from do guard <| (←pairLit' _ _ q(2)) == q((2, 2))
