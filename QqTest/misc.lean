import Qq
open Lean Qq

def bar {α : Q(Type u)} (a : Q($α)) : Q(Prop) := q($a = $a)
def bar2 {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(by simp)

def baz (u : Level) : Type := Q(Sort u)

#guard_msgs(drop info, warning, error) in
#eval bar2 q([1,2, 4])

/-- info: q(∀ (x : Nat), x = x + 0) : Q(Prop) -/
#guard_msgs in
#check q(∀ x, x = x + 0)

example {α : Q(Type u)} (inst : Q(Inhabited $α)) : Q(∃ x : $α, x = x) :=
  q(⟨default, by rfl⟩)

-- TODO: investigate PANIC
-- example : Q(let x := 5; x = x) := q(by simp)

#guard_msgs(drop info, warning, error) in
-- the following also panics if moved into an `example`
#eval show Q(∀ n : UInt64, n.toFin = n.toFin) from q(fun _ => by simp)

def foo' (n : Nat) : Q(Q($($n) = $($n))) := q(q(by simp))

#guard_msgs(drop info, warning, error) in
#eval foo' 3
