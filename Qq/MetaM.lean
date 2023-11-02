import Qq.Macro
import Qq.Delab

open Lean Elab Term Meta

namespace Qq

def mkFreshExprMVarQ (ty : Q(Sort u)) (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Q($ty) := do
  mkFreshExprMVar (some ty) kind userName

def withLocalDeclDQ [Monad n] [MonadControlT MetaM n] (name : Name) (β : Q(Sort u)) (k : Q($β) → n α) : n α :=
  withLocalDeclD name β k

def withLocalDeclQ [Monad n] [MonadControlT MetaM n] (name : Name) (bi : BinderInfo) (β : Q(Sort u)) (k : Q($β) → n α) : n α :=
  withLocalDecl name bi β k

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

def inferTypeQ (e : Expr) : MetaM ((u : Level) × (α : Q(Sort $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← whnf (← inferType α) | throwError "not a type{indentExpr α}"
  pure ⟨u, α, e⟩

def checkTypeQ (e : Expr) (ty : Q(Sort $u)) : MetaM (Option Q($ty)) := do
  if ← isDefEq (← inferType e) ty then
    return some e
  else
    return none

inductive MaybeDefEq {α : Q(Sort $u)} (a b : Q($α)) where
  | defEq : QuotedDefEq a b → MaybeDefEq a b
  | notDefEq : MaybeDefEq a b

instance : Repr (MaybeDefEq a b) where
  reprPrec := fun
    | .defEq _, prec => Repr.addAppParen "defEq _" prec
    | .notDefEq, _ => "notDefEq"

def isDefEqQ {α : Q(Sort $u)} (a b : Q($α)) : MetaM (MaybeDefEq a b) := do
  if ← isDefEq a b then
    return .defEq ⟨⟩
  else
    return .notDefEq

def assertDefEqQ {α : Q(Sort $u)} (a b : Q($α)) : MetaM (PLift (QuotedDefEq a b)) := do
  match ← isDefEqQ a b with
  | .defEq witness => return ⟨witness⟩
  | .notDefEq => throwError "{a} is not definitionally equal to{indentExpr b}"
