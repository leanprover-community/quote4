import Lean

open Lean

instance : ToExpr Int where
  toTypeExpr := mkConst ``Int
  toExpr i := match i with
    | Int.ofNat n => mkApp (mkConst ``Int.ofNat) (toExpr n)
    | Int.negSucc n => mkApp (mkConst ``Int.negSucc) (toExpr n)

instance : ToExpr MVarId where
  toTypeExpr := mkConst ``MVarId
  toExpr i := mkApp (mkConst ``MVarId.mk) (toExpr i.name)

instance : ToExpr FVarId where
  toTypeExpr := mkConst ``FVarId
  toExpr i := mkApp (mkConst ``FVarId.mk) (toExpr i.name)

open Level in
private def toExprLevel : Level → Expr
  | zero _       => mkConst ``levelZero
  | succ l _     => mkApp (mkConst ``mkLevelSucc) (toExprLevel l)
  | Level.max l₁ l₂ _ => mkApp2 (mkConst ``mkLevelMax) (toExprLevel l₁) (toExprLevel l₂)
  | imax l₁ l₂ _ => mkApp2 (mkConst ``mkLevelIMax) (toExprLevel l₁) (toExprLevel l₂)
  | param n _    => mkApp (mkConst ``mkLevelParam) (toExpr n)
  | mvar n _     => mkApp (mkConst ``mkLevelMVar) (toExpr n)

instance : ToExpr Level := ⟨toExprLevel, mkConst ``Level⟩

instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr lit := match lit with
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
  | bvar n _        => mkApp (mkConst ``mkBVar) (mkNatLit n)
  | fvar n _        => mkApp (mkConst ``mkFVar) (toExpr n)
  | mvar n _        => mkApp (mkConst ``mkMVar) (toExpr n)
  | sort l _        => mkApp (mkConst ``mkSort) (toExpr l)
  | const n ls _    => mkApp2 (mkConst ``mkConst) (toExpr n) (toExpr ls)
  | app f x _       => mkApp2 (mkConst ``mkApp) (toExprExpr f) (toExprExpr x)
  | lam x d b c     => mkApp4 (mkConst ``mkLambda)
    (toExpr x) (toExpr c.binderInfo) (toExprExpr d) (toExprExpr b)
  | forallE x d b c => mkApp4 (mkConst ``mkForall)
    (toExpr x) (toExpr c.binderInfo) (toExprExpr d) (toExprExpr b)
  | letE x t v b c  => mkApp5 (mkConst ``mkLet)
    (toExpr x) (toExprExpr t) (toExprExpr v) (toExprExpr b) (toExpr c.nonDepLet)
  | lit (natVal n) _ => mkApp (mkConst ``mkNatLit) (mkNatLit n)
  | lit (strVal s) _ => mkApp (mkConst ``mkStrLit) (mkStrLit s)
  | mdata md e _    => mkApp2 (mkConst ``mkMData) (toExpr md) (toExprExpr e)
  | proj s i e _    => mkApp3 (mkConst ``mkProj) (toExpr s) (mkNatLit i) (toExprExpr e)

instance : ToExpr Expr := ⟨toExprExpr, mkConst ``Expr⟩
