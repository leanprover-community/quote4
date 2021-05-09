import Qq
open Lean Qq

def bar {α : QQ Type u} (a : QQ α) : QQ Prop := qq a = a
def bar2 {α : QQ Sort u} (a : QQ α) : QQ a = a := qq by simp

def baz (u : Level) : Type := QQ Sort u

#eval bar2 (qq [1,2, 4])

#check qq ∀ x, x = x + 0

example {α : QQ Type u} (inst : QQ Inhabited α) : QQ ∃ x : α, x = x :=
  qq ⟨arbitrary, by rfl⟩

example : QQ let x := 5; x = x := qq by simp

#eval show QQ ∀ n : UInt64, n.val = n.val from qq fun _ => by simp

def foo' (n : Nat) : QQ QQ n = n := qq qq by simp
#eval foo' 3
