import Qq.Macro

open Lean Elab Term Meta

namespace Qq

def mkFreshExprMVarQ (ty : Q(Sort u)) (kind := MetavarKind.natural) (userName := Name.anonymous) : MetaM Q($ty) := do
  mkFreshExprMVar ty kind userName

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
  elabTermEnsuringType stx expectedType catchExPostpone implicitLambda errorMsgHeader?
