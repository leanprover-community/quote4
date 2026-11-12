import Qq
import Lean.Elab.Command
open Qq Lean Meta

/-!
# `~q!` structural matching

`~q!(<pattern>)` matches like `~q(<pattern>)`, but the match test runs at
`TransparencyMode.none`: no definitions (not even `@[reducible]` ones) are unfolded,
so constants compare by name.
-/

opaque k : Nat
opaque m : Nat

abbrev double (a : Nat) : Nat := a + a

@[reducible] def addRed (a b : Nat) : Nat := Nat.add a b

def addDef (a b : Nat) : Nat := Nat.add a b

/-- Structural variant: matches only the literal `Nat.add` head. -/
def matchAdd! (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q!(Nat.add $x $y) => return some (x, y)
  | _ => return none

/-- Reducible-defeq control (`~q`). -/
def matchAdd (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q(Nat.add $x $y) => return some (x, y)
  | _ => return none

/-- `+` pattern, structural variant. -/
def matchPlus! (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q!($x + $y) => return some (x, y)
  | _ => return none

/-- `+` pattern, reducible-defeq control. -/
def matchPlus (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q($x + $y) => return some (x, y)
  | _ => return none

/-- Pattern with a reducible constant head, structural variant. -/
def matchAddRed! (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q!(addRed $x $y) => return some (x, y)
  | _ => return none

/-- Pattern with a reducible constant head, reducible-defeq control. -/
def matchAddRed (e : Q(Nat)) : MetaM (Option (Q(Nat) × Q(Nat))) := do
  match e with
  | ~q(addRed $x $y) => return some (x, y)
  | _ => return none

-- TODO: this linter crashes on the `def` below (same as QqTest/hoMatching.lean)
set_option linter.constructorNameAsVariable false in
/-- Higher-order capture must still work structurally (mvar assignment is unaffected). -/
def matchExists! (e : Q(Prop)) : MetaM (Option Q(Nat → Nat → Prop)) := do
  match e with
  | ~q!(∃ x y, $p x y) => return some p
  | _ => return none

/-- Literal constant matching at a higher universe in the structural variant. -/
def matchType3! (e : Q(Type 4)) : MetaM Bool := do
  match e with
  | ~q!(Type 3) => return true
  | _ => return false

/-- Reducible-defeq control for `matchType3!`. -/
def matchType3 (e : Q(Type 4)) : MetaM Bool := do
  match e with
  | ~q(Type 3) => return true
  | _ => return false

/-- A reducible alias for `Type 3`. -/
abbrev MyTy : Type 4 := Type 3

/-- `let ~q!` form. -/
def letMatch! (e : Q(Nat)) : MetaM Nat := do
  let ~q!(Nat.add $x $_y) := e | return 0
  if x == q(k) then return 1 else return 2

/-- `if let ~q!` form. -/
def ifLetMatch! (e : Q(Nat)) : MetaM Nat := do
  if let ~q!($x + $y) := e then
    if x == q(k) && y == q(k) then return 1 else return 2
  else
    return 0

/-- `~q!` nested inside an ordinary constructor pattern (exercises `floatQMatchPairs`). -/
def matchPair! (p : Q(Nat) × Bool) : MetaM Nat := do
  match p with
  | (~q!(Nat.add $x $_y), true) => if x == q(k) then return 1 else return 2
  | _ => return 0

/-- info: true -/
#guard_msgs in
#eval show MetaM Bool from do
  -- `~q` unfolds the `abbrev double` (reducible) and sees through to `k + k`
  let x : Q(Nat) := q(double k)
  match x with
  | ~q($a + $b) => return true
  | _ => return false

/-- info: false -/
#guard_msgs in
#eval show MetaM Bool from do
  -- `~q!` compares structurally: `double k` is not an `HAdd.hAdd` application
  let x : Q(Nat) := q(double k)
  match x with
  | ~q!($a + $b) => return true
  | _ => return false

/-- info: some (Expr.const `k [], Expr.const `m []) -/
#guard_msgs in
#eval show MetaM (Option (Q(Nat) × Q(Nat))) from do
  matchAdd! q(Nat.add k m)

/-- info: none -/
#guard_msgs in
#eval show MetaM (Option (Q(Nat) × Q(Nat))) from do
  -- `k + m` elaborates to `HAdd.hAdd`; structurally different from `Nat.add`
  matchAdd! q(k + m)

run_cmd Lean.Elab.Command.runTermElabM fun _ => do
  let check (msg : String) (b : Bool) : MetaM Unit := unless b do throwError msg

  -- 1. structural match on the exact head, with captures
  let some (x, y) ← matchAdd! q(Nat.add k m) | throwError "1: no match"
  check "1: capture x" (x == q(k))
  check "1: capture y" (y == q(m))

  -- 2. `HAdd.hAdd` vs `Nat.add`: neither variant matches (already true for `~q`)
  check "2: ~q! HAdd" (← matchAdd! q(k + m)).isNone
  check "2: ~q  HAdd" (← matchAdd q(k + m)).isNone

  -- 3. reducible definition in the *discriminant* is not unfolded by `~q!`
  check "3: ~q! addRed discr" (← matchAdd! q(addRed k m)).isNone
  check "3: ~q  addRed discr" (← matchAdd q(addRed k m)).isSome

  -- 4. reducible definition in the *pattern* is not unfolded by `~q!`
  check "4: ~q! addRed pat" (← matchAddRed! q(Nat.add k m)).isNone
  check "4: ~q  addRed pat" (← matchAddRed q(Nat.add k m)).isSome

  -- 5. default-transparency definitions are never unfolded (same for both)
  check "5: ~q! addDef" (← matchAdd! q(addDef k m)).isNone
  check "5: ~q  addDef" (← matchAdd q(addDef k m)).isNone

  -- 6. abbrev unfolding (`double k` is `k + k`): control difference
  check "6: ~q! double" (← matchPlus! q(double k)).isNone
  let some (x, _) ← matchPlus q(double k) | throwError "6: ~q double: no match"
  check "6: ~q double capture" (x == q(k))

  -- 7. higher-order capture `$p x y` still works structurally
  let some p ← matchExists! q(∃ x y, x + 1 ≤ y) | throwError "7: no match"
  -- `p` is captured partially applied (`fun x => LE.le (x + 1)`); applying it to
  -- arguments recovers the body.
  check "7: capture p" (q($p 37 42) == q(37 + 1 ≤ 42))
  check "7: non-match" (← matchExists! q(∀ x : Nat, 0 ≤ x)).isNone

  -- 8. matching at a higher universe (`Type 3` is `Sort 4`)
  check "8: match" (← matchType3! q(Type 3))
  check "8: ~q! abbrev non-match" (not (← matchType3! q(MyTy)))
  check "8: ~q  abbrev match (control)" (← matchType3 q(MyTy))

  -- 9. `let ~q!` and `if let ~q!` forms
  check "9: let (match)" ((← letMatch! q(Nat.add k m)) == 1)
  check "9: let (no match)" ((← letMatch! q(addRed k m)) == 0)
  check "9: if-let (match)" ((← ifLetMatch! q(k + k)) == 1)
  check "9: if-let (no unfold)" ((← ifLetMatch! q(double k)) == 0)

  -- 10. `~q!` nested in a constructor pattern
  check "10: pair (match)" ((← matchPair! (q(Nat.add k m), true)) == 1)
  check "10: pair (no match)" ((← matchPair! (q(addRed k m), true)) == 0)
  check "10: pair (other)" ((← matchPair! (q(Nat.add k m), false)) == 0)
