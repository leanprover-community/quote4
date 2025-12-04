module

public import Qq.Macro
public import Qq.Delab
import Qq.Typ

public section

/-!
# `Qq`-ified spellings of functions in `Lean.Meta`

This file provides variants of the function in the `Lean.Meta` namespace,
which operate with `Q(_)` instead of `Expr`.
-/

open Lean Elab Term Meta

namespace Qq

def mkFreshExprMVarQ (ty : Q(Sort u)) (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Q($ty) := do
  mkFreshExprMVar (some ty) kind userName

def withLocalDeclDQ [Monad n] [MonadControlT MetaM n] (name : Name) (β : Q(Sort u)) (k : Q($β) → n α) : n α :=
  withLocalDeclD name β k

def withLocalDeclQ [Monad n] [MonadControlT MetaM n] (name : Name) (bi : BinderInfo) (β : Q(Sort u)) (k : Q($β) → n α) : n α :=
  withLocalDecl name bi β k

def synthInstanceQ? (α : Q(Sort u)) : MetaM (Option Q($α)) := do
  synthInstance? α

def trySynthInstanceQ (α : Q(Sort u)) : MetaM (LOption Q($α)) := do
  trySynthInstance α

def synthInstanceQ (α : Q(Sort u)) : MetaM Q($α) := do
  synthInstance α

def instantiateMVarsQ {α : Q(Sort u)} (e : Q($α)) : MetaM Q($α) := do
  instantiateMVars e

def elabTermEnsuringTypeQ (stx : Syntax) (expectedType : Q(Sort u))
    (catchExPostpone := true) (implicitLambda := true) (errorMsgHeader? : Option String := none) :
    TermElabM Q($expectedType) := do
  elabTermEnsuringType stx (some expectedType) catchExPostpone implicitLambda errorMsgHeader?

/--
A `Qq`-ified version of `Lean.Meta.inferType`

Instead of writing `let α ← inferType e`, this allows writing `let ⟨u, α, e⟩ ← inferTypeQ e`,
which results in a context of
```
e✝ : Expr
u : Level
α : Q(Type u)
e : Q($α)
```
Here, the new `e` is defeq to the old one, but now has `Qq`-ascribed type information.

This is frequently useful when using the `~q` matching from `QQ/Match.lean`,
as it allows an `Expr` to be turned into something that can be matched upon.
-/
def inferTypeQ (e : Expr) : MetaM ((u : Level) × (α : Q(Sort $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  pure ⟨u, α, e⟩

/-- If `e` is a `ty`, then view it as a term of `Q($ty)`. -/
def checkTypeQ (e : Expr) (ty : Q(Sort $u)) : MetaM (Option Q($ty)) := do
  if ← isDefEq (← inferType e) ty then
    return some e
  else
    return none

/-- The result of `Qq.isDefEqQ`; `MaybeDefEq a b` is an optional version of `$a =Q $b`. -/
inductive MaybeDefEq {α : Q(Sort $u)} (a b : Q($α)) where
  | defEq : QuotedDefEq a b → MaybeDefEq a b
  | notDefEq : MaybeDefEq a b

instance : Repr (MaybeDefEq a b) where
  reprPrec := fun
    | .defEq _, prec => Repr.addAppParen "defEq _" prec
    | .notDefEq, _ => "notDefEq"

/-- A version of `Lean.Meta.isDefEq` which returns a strongly-typed witness rather than a bool. -/
def isDefEqQ {α : Q(Sort $u)} (a b : Q($α)) : MetaM (MaybeDefEq a b) := do
  if ← isDefEq a b then
    return .defEq ⟨⟩
  else
    return .notDefEq

/-- Like `Qq.isDefEqQ`, but throws an error if not defeq. -/
def assertDefEqQ {α : Q(Sort $u)} (a b : Q($α)) : MetaM (PLift (QuotedDefEq a b)) := do
  match ← isDefEqQ a b with
  | .defEq witness => return ⟨witness⟩
  | .notDefEq => throwError "{a} is not definitionally equal to{indentExpr b}"

/-- The result of `Qq.isLevelDefEqQ`; `MaybeLevelDefEq u v` is an optional version of `$u =QL $v`. -/
inductive MaybeLevelDefEq (u v : Level) where
  | defEq : QuotedLevelDefEq u v → MaybeLevelDefEq u v
  | notDefEq : MaybeLevelDefEq u v

instance : Repr (MaybeLevelDefEq u v) where
  reprPrec := fun
    | .defEq _, prec => Repr.addAppParen "defEq _" prec
    | .notDefEq, _ => "notDefEq"

/-- A version of `Lean.Meta.isLevelDefEq` which returns a strongly-typed witness rather than a bool. -/
def isLevelDefEqQ (u v : Level) : MetaM (MaybeLevelDefEq u v) := do
  if ← isLevelDefEq u v then
    return .defEq ⟨⟩
  else
    return .notDefEq

/-- Like `Qq.isLevelDefEqQ`, but throws an error if not defeq. -/
def assertLevelDefEqQ (u v : Level) : MetaM (PLift (QuotedLevelDefEq u v)) := do
  match ← isLevelDefEqQ u v with
  | .defEq witness => return ⟨witness⟩
  | .notDefEq => throwError "{u} and {v} are not definitionally equal"
