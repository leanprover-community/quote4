import Quote
open Lean Quote

def bar {α : quote Type u} (a : quote α) : quote Prop := quote a = a
def bar2 {α : quote Sort u} (a : quote α) : quote a = a := quote by simp

def baz (u : Level) : Type := quote Sort u

#eval bar2 (quote [1,2, 4])

#check quote ∀ x, x = x + 0

example {α : quote Type u} (inst : quote Inhabited α) : quote ∃ x : α, x = x :=
  quote ⟨arbitrary, by rfl⟩

example : quote let x := 5; x = x := quote by simp

#eval show quote ∀ n : UInt64, n.val = n.val from quote fun _ => by simp

def foo' (n : Nat) : quote quote n = n := quote quote by simp
#eval foo' 3
