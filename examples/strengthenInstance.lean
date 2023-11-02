import Qq
open Qq Lean Meta

class Semigroup (M) extends Mul M where
  mul_assoc {a b c : M} : (a*b)*c = a*(b*c)
export Semigroup (mul_assoc)

def maybeReassoc {M : Q(Type $u)} (mul : Q(Mul $M)) (a b : Q($M)) :
    MetaM (Option Q($a*($b*$b) = ($a*$b)*$b)) := do
  let .some inst ← trySynthInstanceQ q(Semigroup $M) | return none
  assertInstancesCommute
  return some q(by rw [mul_assoc])

def maybeReassocAlt {M : Q(Type $u)} (mul : Q(Mul $M)) (a b : Q($M)) :
    MetaM (Option Q($a*($b*$b) = ($a*$b)*$b)) := do
  let .some inst ← trySynthInstanceQ q(Semigroup $M) | return none
  assumeInstancesCommute
  return some q(by rw [mul_assoc])

def maybeReassocPure {M : Q(Type $u)} (mul : Q(Mul $M)) (a b : Q($M)) (semigroup : Q(Semigroup $M)) :
    Q($a*($b*$b) = ($a*$b)*$b) :=
  assumeInstancesCommute'
  q(by rw [mul_assoc])