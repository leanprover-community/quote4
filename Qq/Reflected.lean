import Lean
open Lean

namespace Qq

class Reflected (a : α) where
  reflected : Expr
  deriving BEq

export Reflected (reflected)

instance : ToString (Reflected (a : α)) where
  toString q := toString (reflected a)

instance : Reflected (n : Nat) := ⟨mkNatLit n⟩
instance : Reflected (s : String) := ⟨mkStrLit s⟩
instance : Reflected (b : Bool) := ⟨mkConst $ if b then ``true else ``false⟩

private def reflectName : Name → Expr
  | Name.anonymous => mkConst ``Name.anonymous
  | Name.num n i _ => mkApp2 (mkConst ``Name.mkNum) (reflectName n) (reflected i)
  | Name.str n s _ => mkApp2 (mkConst ``Name.mkStr) (reflectName n) (reflected s)

instance : Reflected (n : Name) := ⟨reflectName n⟩

private def reflectLit : Literal → Expr
  | Literal.natVal n => mkApp (mkConst ``Literal.natVal) (reflected n)
  | Literal.strVal s => mkApp (mkConst ``Literal.strVal) (reflected s)

instance : Reflected (l : Literal) := ⟨reflectLit l⟩

instance {bi} : Reflected (bi : BinderInfo) :=
  match bi with
    | BinderInfo.default => ⟨mkConst ``BinderInfo.default⟩
    | BinderInfo.implicit => ⟨mkConst ``BinderInfo.implicit⟩
    | BinderInfo.strictImplicit => ⟨mkConst ``BinderInfo.strictImplicit⟩
    | BinderInfo.instImplicit => ⟨mkConst ``BinderInfo.instImplicit⟩
    | BinderInfo.auxDecl => ⟨mkConst ``BinderInfo.auxDecl⟩
