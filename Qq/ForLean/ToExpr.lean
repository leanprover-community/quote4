import Lean

open Lean

instance : ToExpr Int where
  toTypeExpr := mkConst ``Int
  toExpr i := match i with
    | .ofNat n => mkApp (mkConst ``Int.ofNat) (toExpr n)
    | .negSucc n => mkApp (mkConst ``Int.negSucc) (toExpr n)

instance : ToExpr MVarId where
  toTypeExpr := mkConst ``MVarId
  toExpr i := mkApp (mkConst ``MVarId.mk) (toExpr i.name)

instance : ToExpr FVarId where
  toTypeExpr := mkConst ``FVarId
  toExpr i := mkApp (mkConst ``FVarId.mk) (toExpr i.name)

open Level in
private def toExprLevel : Level → Expr
  | zero       => mkConst ``zero
  | succ l     => mkApp (mkConst ``succ) (toExprLevel l)
  | .max l₁ l₂ => mkApp2 (mkConst ``Level.max) (toExprLevel l₁) (toExprLevel l₂)
  | imax l₁ l₂ => mkApp2 (mkConst ``imax) (toExprLevel l₁) (toExprLevel l₂)
  | param n    => mkApp (mkConst ``param) (toExpr n)
  | mvar n     => mkApp (mkConst ``mvar) (toExpr n)

instance : ToExpr Level := ⟨toExprLevel, mkConst ``Level⟩

instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr lit := match lit with
    | .natVal n => mkApp (mkConst ``Literal.natVal) (toExpr n)
    | .strVal s => mkApp (mkConst ``Literal.strVal) (toExpr s)

instance : ToExpr BinderInfo where
  toTypeExpr := mkConst ``BinderInfo
  toExpr bi := match bi with
    | .default => mkConst ``BinderInfo.default
    | .implicit => mkConst ``BinderInfo.implicit
    | .strictImplicit => mkConst ``BinderInfo.strictImplicit
    | .instImplicit => mkConst ``BinderInfo.instImplicit
    | .auxDecl => mkConst ``BinderInfo.auxDecl

instance : ToExpr MData where
  toTypeExpr := mkConst ``MData
  toExpr md := Id.run do
    let mut e := mkConst ``MData.empty
    for (k, v) in md do
      let k := toExpr k
      e := open DataValue in match v with
      | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (toExpr v)
      | ofBool v   => mkApp3 (mkConst ``KVMap.setBool) e k (toExpr v)
      | ofName v   => mkApp3 (mkConst ``KVMap.setName) e k (toExpr v)
      | ofNat v    => mkApp3 (mkConst ``KVMap.setNat) e k (toExpr v)
      | ofInt v    => mkApp3 (mkConst ``KVMap.setInt) e k (toExpr v)
      | ofSyntax v => e -- TODO
    e

open Expr Literal in
private def toExprExpr : Expr → Expr
  | bvar n        => mkApp (mkConst ``bvar) (mkNatLit n)
  | fvar n        => mkApp (mkConst ``fvar) (toExpr n)
  | mvar n        => mkApp (mkConst ``mvar) (toExpr n)
  | sort l        => mkApp (mkConst ``sort) (toExpr l)
  | const n ls    => mkApp2 (mkConst ``const) (toExpr n) (toExpr ls)
  | app f x       => mkApp2 (mkConst ``app) (toExprExpr f) (toExprExpr x)
  | lam x d b c     => mkApp4 (mkConst ``lam) (toExpr x) (toExprExpr d) (toExprExpr b) (toExpr c)
  | forallE x d b c => mkApp4 (mkConst ``forallE) (toExpr x) (toExprExpr d) (toExprExpr b) (toExpr c)
  | letE x t v b c  => mkApp5 (mkConst ``letE) (toExpr x) (toExprExpr t) (toExprExpr v) (toExprExpr b) (toExpr c)
  | lit l         => mkApp (mkConst ``lit) (toExpr l)
  | mdata md e    => mkApp2 (mkConst ``mdata) (toExpr md) (toExprExpr e)
  | proj s i e    => mkApp3 (mkConst ``proj) (toExpr s) (mkNatLit i) (toExprExpr e)

instance : ToExpr Expr := ⟨toExprExpr, mkConst ``Expr⟩
