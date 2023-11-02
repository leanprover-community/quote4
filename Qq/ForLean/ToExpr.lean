import Lean

open Lean

instance : ToExpr Int where
  toTypeExpr := .const ``Int []
  toExpr i := match i with
    | .ofNat n => mkApp (.const ``Int.ofNat []) (toExpr n)
    | .negSucc n => mkApp (.const ``Int.negSucc []) (toExpr n)

instance : ToExpr MVarId where
  toTypeExpr := .const ``MVarId []
  toExpr i := mkApp (.const ``MVarId.mk []) (toExpr i.name)

instance : ToExpr LevelMVarId where
  toTypeExpr := .const ``LevelMVarId []
  toExpr i := mkApp (.const ``LevelMVarId.mk []) (toExpr i.name)

instance : ToExpr FVarId where
  toTypeExpr := .const ``FVarId []
  toExpr i := mkApp (.const ``FVarId.mk []) (toExpr i.name)

open Level in
private def toExprLevel : Level → Expr
  | zero       => .const ``zero []
  | succ l     => mkApp (.const ``succ []) (toExprLevel l)
  | .max l₁ l₂ => mkApp2 (.const ``Level.max []) (toExprLevel l₁) (toExprLevel l₂)
  | imax l₁ l₂ => mkApp2 (.const ``imax []) (toExprLevel l₁) (toExprLevel l₂)
  | param n    => mkApp (.const ``param []) (toExpr n)
  | mvar n     => mkApp (.const ``mvar []) (toExpr n)

instance : ToExpr Level := ⟨toExprLevel, .const ``Level []⟩

instance : ToExpr Literal where
  toTypeExpr := .const ``Literal []
  toExpr lit := match lit with
    | .natVal n => mkApp (.const ``Literal.natVal []) (toExpr n)
    | .strVal s => mkApp (.const ``Literal.strVal []) (toExpr s)

instance : ToExpr BinderInfo where
  toTypeExpr := .const ``BinderInfo []
  toExpr bi := match bi with
    | .default => .const ``BinderInfo.default []
    | .implicit => .const ``BinderInfo.implicit []
    | .strictImplicit => .const ``BinderInfo.strictImplicit []
    | .instImplicit => .const ``BinderInfo.instImplicit []

instance : ToExpr MData where
  toTypeExpr := .const ``MData []
  toExpr md := Id.run do
    let mut e := .const ``MData.empty []
    for (k, v) in md do
      let k := toExpr k
      e := open DataValue in match v with
      | ofString v => mkApp3 (.const ``KVMap.setString []) e k (toExpr v)
      | ofBool v   => mkApp3 (.const ``KVMap.setBool []) e k (toExpr v)
      | ofName v   => mkApp3 (.const ``KVMap.setName []) e k (toExpr v)
      | ofNat v    => mkApp3 (.const ``KVMap.setNat []) e k (toExpr v)
      | ofInt v    => mkApp3 (.const ``KVMap.setInt []) e k (toExpr v)
      | ofSyntax _ => e -- TODO
    e

open Expr Literal in
private def toExprExpr : Expr → Expr
  | bvar n        => mkApp (.const ``bvar []) (mkNatLit n)
  | fvar n        => mkApp (.const ``fvar []) (toExpr n)
  | mvar n        => mkApp (.const ``mvar []) (toExpr n)
  | sort l        => mkApp (.const ``sort []) (toExpr l)
  | const n ls    => mkApp2 (.const ``const []) (toExpr n) (toExpr ls)
  | app f x       => mkApp2 (.const ``app []) (toExprExpr f) (toExprExpr x)
  | lam x d b c     => mkApp4 (.const ``lam []) (toExpr x) (toExprExpr d) (toExprExpr b) (toExpr c)
  | forallE x d b c => mkApp4 (.const ``forallE []) (toExpr x) (toExprExpr d) (toExprExpr b) (toExpr c)
  | letE x t v b c  => mkApp5 (.const ``letE []) (toExpr x) (toExprExpr t) (toExprExpr v) (toExprExpr b) (toExpr c)
  | lit l         => mkApp (.const ``lit []) (toExpr l)
  | mdata md e    => mkApp2 (.const ``mdata []) (toExpr md) (toExprExpr e)
  | proj s i e    => mkApp3 (.const ``proj []) (toExpr s) (mkNatLit i) (toExprExpr e)

instance : ToExpr Expr := ⟨toExprExpr, .const ``Expr []⟩
