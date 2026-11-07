import Qq

open Lean Qq

/-!
Regression tests for <https://github.com/leanprover-community/quote4/issues/16>:
level antiquotations `$u` inside explicit universe annotations `x.{$u}`.
-/

-- The four examples from the issue. The first two used to fail with
-- `unknown universe level '«$u»'`; all four elaborate now.
example (u : Level) (T : Q(Sort u)) (t : Q($T)) := q(@id.{$u} $T $t)
example (u : Level) (T : Q(Sort $u)) (t : Q($T)) := q(@id.{$u} $T $t)
example (u : Level) (T : Q(Sort u)) (t : Q($T)) := q(@id.{u} $T $t)
example (u : Level) (T : Q(Sort $u)) (t : Q($T)) := q(@id.{u} $T $t)

-- `$u` and `u` in an explicit universe annotation produce the same quotation.
example (u : Level) (T : Q(Sort u)) (t : Q($T)) :
    q(@id.{$u} $T $t) = q(@id.{u} $T $t) := rfl

-- Several explicit universe levels, including mixed antiquotations.
example (u v : Level) (A : Q(Type u)) (B : Q(Type v)) (a : Q($A)) (b : Q($B)) :
    Q($A × $B) := q(@Prod.mk.{$u, $v} $A $B $a $b)

example (u v : Level) (A : Q(Sort u)) (B : Q(Sort v)) (a : Q($A)) (b : Q($B)) :
    Q($A) := q(@Function.const.{$u, $v} $A $B $a $b)

-- The antiquotation can refer to a level variable introduced by `variable`.
variable (u : Level) (T : Q(Sort u)) (t : Q($T))

/-- info: q(id «$t») : Q(«$T») -/
#guard_msgs in
#check q(@id.{$u} $T $t)
