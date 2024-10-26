import Qq
open Lean Qq

def bar {α : Q(Type u)} (a : Q($α)) : Q(Prop) := q($a = $a)
def bar2 {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(by simp)

def baz (u : Level) : Type := Q(Sort u)

#eval bar2 q([1,2, 4])

#check q(∀ x, x = x + 0)

example {α : Q(Type u)} (inst : Q(Inhabited $α)) : Q(∃ x : $α, x = x) :=
  q(⟨default, by rfl⟩)

example : Q(let x := 5; x = x) := q(by simp)

#eval show Q(∀ n : UInt64, n.val = n.val) from q(fun _ => by simp)

def foo' (n : Nat) : Q(Q($($n) = $($n))) := q(q(by simp))
#eval foo' 3

#eval (Meta.ReduceEval.reduceEval q(15 + 7 : Fin (2 ^ 4)) : MetaM (Fin (2 ^ 4)))
#eval (Meta.ReduceEval.reduceEval q(15#4 + 7#4 : BitVec 4) : MetaM (BitVec 4))
#eval (Meta.ReduceEval.reduceEval q(15 + 7 : UInt64) : MetaM UInt64)

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  Meta.ReduceEval ?m.2036
-/
#guard_msgs in
#eval Meta.ReduceEval.reduceEval q(15 : USize)
