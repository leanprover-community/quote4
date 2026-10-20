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

-- Regression tests for https://github.com/leanprover-community/quote4/issues/105:
-- the auxiliary local declaration referring to the enclosing `def`/`example` used to be
-- copied into the unquoted context of `q(·)` without its `auxDeclToFullName` entry,
-- panicking `Lean.instantiateLCtxMVars` as soon as a tactic block was elaborated.
example : Q(let x := 5; x = x) := q(by simp)

example : Q(5 = 5) := q(by simp)

def auxDeclQuotedType : Q(5 = 5) := q(by simp)

-- the enclosing declaration's type is not quoted but has a `ToExpr` instance
def auxDeclToExprType : Nat :=
  let _x : Q(Nat) := q(by exact 3)
  1

-- the enclosing declaration's type is a `QuotedDefEq`
theorem auxDeclDefEqType : q(1 + 1) =Q q(2) := by
  let _x : Q(Nat) := q(by exact 1 + 1)
  exact ⟨⟩

-- the following used to panic if moved into an `example`
example : Q(∀ n : UInt64, n.toFin = n.toFin) := q(fun _ => by simp)

#guard_msgs(drop info, warning, error) in
#eval show Q(∀ n : UInt64, n.toFin = n.toFin) from q(fun _ => by simp)

def foo' (n : Nat) : Q(Q($($n) = $($n))) := q(q(by simp))

#guard_msgs(drop info, warning, error) in
#eval foo' 3
