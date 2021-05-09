import Lean
open Lean

instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr l := match l with
    | Literal.natVal n => mkApp (mkConst ``Literal.natVal) (toExpr n)
    | Literal.strVal s => mkApp (mkConst ``Literal.strVal) (toExpr s)

instance : ToExpr BinderInfo where
  toTypeExpr := mkConst ``BinderInfo
  toExpr bi := match bi with
    | BinderInfo.default => mkConst ``BinderInfo.default
    | BinderInfo.implicit => mkConst ``BinderInfo.implicit
    | BinderInfo.strictImplicit => mkConst ``BinderInfo.strictImplicit
    | BinderInfo.instImplicit => mkConst ``BinderInfo.instImplicit
    | BinderInfo.auxDecl => mkConst ``BinderInfo.auxDecl
