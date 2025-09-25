import Qq
open Lean Qq

def bar {α : Q(Type u)} (a : Q($α)) : Q(Prop) := q($a = $a)
def bar2 {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(by simp)

def baz (u : Level) : Type := Q(Sort u)

/--
info: ((Expr.const `of_eq_true []).app
      ((((Expr.const `Eq [Level.zero.succ]).app ((Expr.const `List [Level.zero]).app (Expr.const `Nat []))).app
            ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
                  ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                        (Expr.lit (Literal.natVal 1))).app
                    ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 1))))).app
              ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
                    ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                          (Expr.lit (Literal.natVal 2))).app
                      ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 2))))).app
                ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
                      ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                            (Expr.lit (Literal.natVal 4))).app
                        ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 4))))).app
                  ((Expr.const `List.nil [Level.zero]).app (Expr.const `Nat [])))))).app
        ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
              ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 1))).app
                ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 1))))).app
          ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
                ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                      (Expr.lit (Literal.natVal 2))).app
                  ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 2))))).app
            ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
                  ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                        (Expr.lit (Literal.natVal 4))).app
                    ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 4))))).app
              ((Expr.const `List.nil [Level.zero]).app (Expr.const `Nat []))))))).app
  (((Expr.const `eq_self [Level.zero.succ]).app ((Expr.const `List [Level.zero]).app (Expr.const `Nat []))).app
    ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
          ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 1))).app
            ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 1))))).app
      ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
            ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 2))).app
              ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 2))))).app
        ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Nat [])).app
              ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 4))).app
                ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 4))))).app
          ((Expr.const `List.nil [Level.zero]).app (Expr.const `Nat []))))))
-/
#guard_msgs in
#eval bar2 q([1,2, 4])

/-- info: q(∀ (x : Nat), x = x + 0) : Q(Prop) -/
#guard_msgs in
#check q(∀ x, x = x + 0)

example {α : Q(Type u)} (inst : Q(Inhabited $α)) : Q(∃ x : $α, x = x) :=
  q(⟨default, by rfl⟩)

-- TODO: investigate PANIC
-- example : Q(let x := 5; x = x) := q(by simp)

/--
warning: `UInt64.val` has been deprecated: Use `UInt64.toFin` instead
---
warning: `UInt64.val` has been deprecated: Use `UInt64.toFin` instead
---
info: Expr.lam `x (Expr.const `UInt64 [])
  (((Expr.const `of_eq_true []).app
        ((((Expr.const `Eq [Level.zero.succ]).app ((Expr.const `Fin []).app (Expr.const `UInt64.size []))).app
              ((Expr.const `UInt64.val []).app (Expr.bvar 0))).app
          ((Expr.const `UInt64.val []).app (Expr.bvar 0)))).app
    (((Expr.const `eq_self [Level.zero.succ]).app ((Expr.const `Fin []).app (Expr.const `UInt64.size []))).app
      ((Expr.const `UInt64.val []).app (Expr.bvar 0))))
  BinderInfo.default
-/
#guard_msgs in
#eval show Q(∀ n : UInt64, n.val = n.val) from q(fun _ => by simp)

def foo' (n : Nat) : Q(Q($($n) = $($n))) := q(q(by simp))

/--
info: ((Expr.const `Qq.Quoted.unsafeMk []).app
      (((Expr.const `Lean.Expr.app []).app
            (((Expr.const `Lean.Expr.app []).app
                  (((Expr.const `Lean.Expr.app []).app
                        (((Expr.const `Lean.Expr.const []).app
                              ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "Eq")))).app
                          ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Lean.Level [])).app
                                ((Expr.const `Lean.Level.succ []).app (Expr.const `Lean.Level.zero []))).app
                            ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
                    (((Expr.const `Lean.Expr.const []).app
                          ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "Nat")))).app
                      ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
              ((((Expr.const `Lean.ToExpr.toExpr [Level.zero]).app (Expr.const `Nat [])).app
                    (Expr.const `Lean.instToExprNat [])).app
                ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                      (Expr.lit (Literal.natVal 3))).app
                  ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 3))))))).app
        ((((Expr.const `Lean.ToExpr.toExpr [Level.zero]).app (Expr.const `Nat [])).app
              (Expr.const `Lean.instToExprNat [])).app
          ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 3))).app
            ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 3))))))).app
  (((Expr.const `Lean.Expr.app []).app
        (((Expr.const `Lean.Expr.app []).app
              (((Expr.const `Lean.Expr.const []).app
                    ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "of_eq_true")))).app
                ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level [])))).app
          (((Expr.const `Lean.Expr.app []).app
                (((Expr.const `Lean.Expr.app []).app
                      (((Expr.const `Lean.Expr.app []).app
                            (((Expr.const `Lean.Expr.const []).app
                                  ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "Eq")))).app
                              ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Lean.Level [])).app
                                    ((Expr.const `Lean.Level.succ []).app (Expr.const `Lean.Level.zero []))).app
                                ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
                        (((Expr.const `Lean.Expr.const []).app
                              ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "Nat")))).app
                          ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
                  ((((Expr.const `Lean.ToExpr.toExpr [Level.zero]).app (Expr.const `Nat [])).app
                        (Expr.const `Lean.instToExprNat [])).app
                    ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app
                          (Expr.lit (Literal.natVal 3))).app
                      ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 3))))))).app
            ((((Expr.const `Lean.ToExpr.toExpr [Level.zero]).app (Expr.const `Nat [])).app
                  (Expr.const `Lean.instToExprNat [])).app
              ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 3))).app
                ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 3)))))))).app
    (((Expr.const `Lean.Expr.app []).app
          (((Expr.const `Lean.Expr.app []).app
                (((Expr.const `Lean.Expr.const []).app
                      ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "eq_self")))).app
                  ((((Expr.const `List.cons [Level.zero]).app (Expr.const `Lean.Level [])).app
                        ((Expr.const `Lean.Level.succ []).app (Expr.const `Lean.Level.zero []))).app
                    ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
            (((Expr.const `Lean.Expr.const []).app
                  ((Expr.const `Lean.Name.mkStr1 []).app (Expr.lit (Literal.strVal "Nat")))).app
              ((Expr.const `List.nil [Level.zero]).app (Expr.const `Lean.Level []))))).app
      ((((Expr.const `Lean.ToExpr.toExpr [Level.zero]).app (Expr.const `Nat [])).app
            (Expr.const `Lean.instToExprNat [])).app
        ((((Expr.const `OfNat.ofNat [Level.zero]).app (Expr.const `Nat [])).app (Expr.lit (Literal.natVal 3))).app
          ((Expr.const `instOfNatNat []).app (Expr.lit (Literal.natVal 3)))))))
-/
#guard_msgs in
#eval foo' 3
