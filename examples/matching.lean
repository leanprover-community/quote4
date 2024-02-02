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

def pairLit (u : Lean.Level) (α : Q(Type u)) (a : Q($α)) : MetaM Q($α × $α) := do
  match u, α, a with
  | 0, ~q(Nat), n => return q(($n, $n))
  | 0, ~q(Int), z => return q(($z, $z))
  | _, _, _ => failure

#eval show MetaM Unit from do guard <| (←pairLit _ _ q(2)) == q((2, 2))
