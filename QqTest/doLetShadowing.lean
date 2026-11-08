import Qq
import Lean.Elab.Command

open Qq Lean Meta Elab Term Command

/-!
Regression tests for https://github.com/leanprover-community/quote4/issues/8

A `do`-block `let` without a type annotation used to be silently dropped from a quotation's
unquoted local context whenever its (still metavariable) type could not yet be recognized as
quotable. Later declarations referring to it — like `depth` below, whose value mentions the
shadowing `args` — were then left with a dangling reference, failing with
`unknown free variable '_uniq.N'` at an unrelated antiquotation.
-/

set_option linter.checkUnivs false

abbrev TypeFun.{u,v} (n : Nat) : Type ((max u v) + 1)
  := (Fin n → Type u) → Type v

def CurriedTypeFun.{u,v} : Nat → Type ((max u v) + 1)
  | 0   => ULift.{v+1,u+1} (Type u)
  | 1   => Type u → Type v
  | n+1 => Type u → CurriedTypeFun n

def TypeFun.ofCurried {n : Nat} (_ : CurriedTypeFun n) : TypeFun n := fun _ => Nat

/-- The issue's MWE: the unannotated shadowing `let args := a :: args` must not break the
quotation below. -/
def shadowedUnannotatedDoLet : Expr → List Expr → TermElabM Expr
  | Expr.app F a, args => do
    let args := a :: args
    let depth : Nat := args.length
    let F : Q(CurriedTypeFun.{0,0} $depth) := F
    let F : Q(TypeFun.{0,0} $depth) := q(@TypeFun.ofCurried $depth $F)
    pure F
  | _, _ => throwError ""

-- The result of the quotation refers to the unquotable `Expr` input and the let-bound `Nat`.
run_cmd liftTermElabM do
  let e ← shadowedUnannotatedDoLet (.app (.const ``Nat.succ []) (.const ``Nat.zero [])) []
  -- `q(@TypeFun.ofCurried $depth $F)` with `depth = 1` and `F = Nat.succ`;
  -- `ToExpr Nat` produces the type-correct `OfNat.ofNat` representation of numerals.
  let one := mkApp3 (.const ``OfNat.ofNat [.zero]) (.const ``Nat []) (.lit (.natVal 1))
    (mkApp (.const ``instOfNatNat []) (.lit (.natVal 1)))
  let expected := mkApp2 (.const ``TypeFun.ofCurried [.zero, .zero, .zero]) one
    (.const ``Nat.succ [])
  unless e == expected do
    throwError "unexpected quotation result:{indentD m!"{e}"}"

/-- A chain of dependent unannotated `let`s, the last of which feeds a quotation. -/
def chainedUnannotatedDoLets : MetaM Q(Nat) := do
  let xs := [1, 2, 3]
  let n := xs.length
  let m := n + 1
  return q($m * 2)

-- The let-bound `Nat` is quoted by `ToExpr`, evaluating to its value.
run_cmd liftTermElabM do
  let e ← chainedUnannotatedDoLets
  unless e == q(4 * 2) do
    throwError "unexpected quotation result:{indentD m!"{e}"}"
