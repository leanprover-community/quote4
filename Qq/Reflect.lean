import Lean
open Lean

namespace Qq

class Reflect (α : Type u) where
  reflectUniv : Level
  reflectTy : Expr
  reflect : α → Expr

export Reflect (reflect)
open Reflect

instance : ToString (Reflect α) where
  toString q := toString (reflectTy α)

instance : Reflect Nat := ⟨levelZero, mkConst ``Nat, mkNatLit⟩

instance : Reflect String := ⟨levelZero, mkConst ``String, mkStrLit⟩

instance : Reflect Bool where
  reflectUniv := levelZero
  reflectTy := mkConst ``Bool
  reflect b := mkConst $ if b then ``true else ``false

instance : Reflect Int where
  reflectUniv := levelZero
  reflectTy := mkConst ``Int
  reflect i := match i with
    | Int.ofNat n => mkApp (mkConst ``Int.ofNat) (reflect n)
    | Int.negSucc n => mkApp (mkConst ``Int.negSucc) (reflect n)

instance [Reflect α] : Reflect (Option α) where
  reflectUniv := reflectUniv α
  reflectTy := mkApp (mkConst ``Option [reflectUniv α]) (reflectTy α)
  reflect x := match x with
    | none => mkApp (mkConst ``Option.none [reflectUniv α]) (reflectTy α)
    | some x => mkApp2 (mkConst ``Option.some [reflectUniv α]) (reflectTy α) (reflect x)

private def reflectList [Reflect α] : List α → Expr
  | List.nil => mkApp (mkConst ``List.nil [reflectUniv α]) (reflectTy α)
  | List.cons x xs => mkApp3 (mkConst ``List.cons [reflectUniv α]) (reflectTy α) (reflect x) (reflectList xs)

instance [Reflect α] : Reflect (List α) where
  reflectUniv := reflectUniv α
  reflectTy := mkApp (mkConst ``List [reflectUniv α]) (reflectTy α)
  reflect := reflectList

private def reflectName : Name → Expr
  | Name.anonymous => mkConst ``Name.anonymous
  | Name.num n i _ => mkApp2 (mkConst ``Name.mkNum) (reflectName n) (reflect i)
  | Name.str n s _ => mkApp2 (mkConst ``Name.mkStr) (reflectName n) (reflect s)

instance : Reflect Name := ⟨levelZero, mkConst ``Name, reflectName⟩

open Level in
private def reflectLevel : Level → Expr
  | zero _       => mkConst ``levelZero
  | succ l _     => mkApp (mkConst ``mkLevelSucc) (reflectLevel l)
  | Level.max l₁ l₂ _ => mkApp2 (mkConst ``mkLevelMax) (reflectLevel l₁) (reflectLevel l₂)
  | imax l₁ l₂ _ => mkApp2 (mkConst ``mkLevelIMax) (reflectLevel l₁) (reflectLevel l₂)
  | param n _    => mkApp (mkConst ``mkLevelParam) (reflect n)
  | mvar n _     => mkApp (mkConst ``mkLevelMVar) (reflect n)

instance : Reflect Level := ⟨levelZero, mkConst ``Level, reflectLevel⟩

private def reflectLit : Literal → Expr
  | Literal.natVal n => mkApp (mkConst ``Literal.natVal) (reflect n)
  | Literal.strVal s => mkApp (mkConst ``Literal.strVal) (reflect s)

instance : Reflect Literal := ⟨levelZero, mkConst ``Literal, reflectLit⟩

instance : Reflect BinderInfo where
  reflectUniv := levelZero
  reflectTy := mkConst ``BinderInfo
  reflect bi := match bi with
    | BinderInfo.default => mkConst ``BinderInfo.default
    | BinderInfo.implicit => mkConst ``BinderInfo.implicit
    | BinderInfo.strictImplicit => mkConst ``BinderInfo.strictImplicit
    | BinderInfo.instImplicit => mkConst ``BinderInfo.instImplicit
    | BinderInfo.auxDecl => mkConst ``BinderInfo.auxDecl

open DataValue in
private def reflectMData (md : MData) : Expr := do
  let mut e := mkConst ``MData.empty
  for (k, v) in md do
    let k := reflect k
    e := match v with
    | ofString v => mkApp3 (mkConst ``KVMap.setString) e k (mkStrLit v)
    | ofBool v   => mkApp3 (mkConst ``KVMap.setBool) e k (reflect v)
    | ofName v   => mkApp3 (mkConst ``KVMap.setName) e k (reflect v)
    | ofNat v    => mkApp3 (mkConst ``KVMap.setNat) e k (mkNatLit v)
    | ofInt v    => mkApp3 (mkConst ``KVMap.setInt) e k (reflect v)
  e

instance : Reflect MData := ⟨levelZero, mkConst ``MData, reflectMData⟩

open Expr Literal in
private def reflectExpr : Expr → Expr
  | bvar n _        => mkApp (mkConst ``mkBVar) (mkNatLit n)
  | fvar n _        => mkApp (mkConst ``mkFVar) (reflect n)
  | mvar n _        => mkApp (mkConst ``mkMVar) (reflect n)
  | sort l _        => mkApp (mkConst ``mkSort) (reflect l)
  | const n ls _    => mkApp2 (mkConst ``mkConst) (reflect n) (reflect ls)
  | app f x _       => mkApp2 (mkConst ``mkApp) (reflectExpr f) (reflectExpr x)
  | lam x d b c     => mkApp4 (mkConst ``mkLambda)
    (reflect x) (reflect c.binderInfo) (reflectExpr d) (reflectExpr b)
  | forallE x d b c => mkApp4 (mkConst ``mkForall)
    (reflect x) (reflect c.binderInfo) (reflectExpr d) (reflectExpr b)
  | letE x t v b c  => mkApp5 (mkConst ``mkLet)
    (reflect x) (reflectExpr t) (reflectExpr v) (reflectExpr b) (reflect c.nonDepLet)
  | lit (natVal n) _ => mkApp (mkConst ``mkNatLit) (mkNatLit n)
  | lit (strVal s) _ => mkApp (mkConst ``mkStrLit) (mkStrLit s)
  | mdata md e _    => mkApp2 (mkConst ``mkMData) (reflect md) (reflectExpr e)
  | proj s i e _    => mkApp3 (mkConst ``mkProj) (reflect s) (mkNatLit i) (reflectExpr e)

instance : Reflect Expr := ⟨levelZero, mkConst ``Expr, reflectExpr⟩
