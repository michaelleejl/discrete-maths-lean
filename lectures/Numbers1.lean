import Mathlib.Data.Nat.Basic
import Mathlib.Logic.ExistsUnique

open Nat

----------------------------- Lecture 05 -----------------------------

-- Definition 43
structure Monoid (X : Type) where
  e : X
  op : X → X → X
  l_neu : ∀ x : X, op e x = x
  r_neu : ∀ x : X, op x e = x
  assoc : ∀ x y z : X, op (op x y) z = op x (op y z)

def ListMonoid (a : Type) : Monoid (List a) where
  e := []
  op := List.append
  l_neu := List.nil_append
  r_neu := List.append_nil
  assoc := List.append_assoc

def NatAddMonoid : Monoid Nat where
  e := 0
  op := Nat.add
  l_neu := Nat.zero_add
  r_neu := Nat.add_zero
  assoc := Nat.add_assoc

def NatMulMonoid : Monoid Nat where
  e := 1
  op := Nat.mul
  l_neu := Nat.one_mul
  r_neu := Nat.mul_one
  assoc := Nat.mul_assoc

-- Definition 43b
structure CommutativeMonoid (X : Type) extends Monoid X where
 comms : ∀ x y : X, op x y = op y x

def NatAddCommMonoid : CommutativeMonoid Nat :=
  { NatAddMonoid with
    comms := Nat.add_comm }


def NatMulCommMonoid : CommutativeMonoid Nat :=
  { NatMulMonoid with
    comms := Nat.mul_comm }

----------------------------- Lecture 06 -----------------------------

-- Definition 44
structure Semiring (X : Type) where
  plus : CommutativeMonoid X
  mul    : Monoid X
  dest_l : ∀ x : X, mul.op plus.e x = plus.e
  dest_r : ∀ x : X, mul.op x plus.e = plus.e
  dist_l : ∀ x y z : X,
    mul.op x (plus.op y z) = plus.op (mul.op x y) (mul.op x z)
  dist_r : ∀ y z x : X,
    mul.op (plus.op y z) x = plus.op (mul.op y x) (mul.op z x)

structure CommutativeSemiring (X : Type) where
  plus : CommutativeMonoid X
  mul    : CommutativeMonoid X
  dest_l : ∀ x : X, mul.op plus.e x = plus.e
  dest_r : ∀ x : X, mul.op x plus.e = plus.e
  dist_l : ∀ x y z : X,
    mul.op x (plus.op y z) = plus.op (mul.op x y) (mul.op x z)
  dist_r : ∀ y z x : X,
    mul.op (plus.op y z) x = plus.op (mul.op y x) (mul.op z x)

def NatAddMulCommutativeSemiring : CommutativeSemiring Nat where
  plus := NatAddCommMonoid
  mul  := NatMulCommMonoid
  dest_l := Nat.zero_mul
  dest_r := Nat.mul_zero
  dist_l := Nat.mul_add
  dist_r := Nat.add_mul

-- Definition 45
def cancellable_left {X : Type} (op : X → X → X) (c : X) :=
  ∀ x y : X, op c x = op c y → x = y

def cancellable_right {X : Type} (op : X → X → X) (c : X) :=
  ∀ x y : X, op x c = op y c → x = y

def cancellable {X : Type} (op : X → X → X) (c : X) :=
  cancellable_left op c ∧ cancellable_right op c

example {X : Type} : ∀ (xs : List X), cancellable (List.append) xs
  := by intro xs
        dsimp [cancellable, cancellable_left, cancellable_right]
        constructor
        · intros x y
          exact List.append_cancel_left
        · intros x y
          exact List.append_cancel_right

def monoid_left_inverse {X : Type} (M : Monoid X) (l x : X)
  := M.op l x = M.e

def monoid_right_inverse {X : Type} (M : Monoid X) (x r : X)
  := M.op x r = M.e

def monoid_inverse {X : Type} (M : Monoid X) (x y : X)
  := monoid_left_inverse M y x ∧ monoid_right_inverse M x y

-- Proposition 47
theorem uniqueness_of_monoid_inverse {X : Type} :
    ∀ (M : Monoid X) (x l r : X),
    monoid_left_inverse M l x ∧ monoid_right_inverse M x r →
    l = r
  := by intros M x l r
        dsimp [monoid_left_inverse, monoid_right_inverse]
        intros h
        match h with
          | ⟨ hl, hr ⟩ =>
              calc
              l = M.op l M.e        := (M.r_neu l).symm
              _ = M.op l (M.op x r) := by rw [hr]
              _ = M.op (M.op l x) r := (M.assoc l x r).symm
              _ = M.op M.e r        := by rw [hl]
              _ = r                 := M.l_neu r


structure Group (X : Type) extends Monoid X where
  invers : ∀ x : X, ∃ y : X, monoid_inverse (toMonoid) x y

structure AbelianGroup (X : Type) extends CommutativeMonoid X where
  invers : ∀ x : X, ∃ y : X, monoid_inverse (toMonoid) x y

-- Definition 50
def admits_additive_inverse (n : ℕ) : Prop := ∃ m : ℕ, n + m = 0

example : admits_additive_inverse 0
  := by exists 0

def admits_multiplicative_inverse (n : ℕ) : Prop := ∃ m : ℕ, n * m = 1

example : admits_multiplicative_inverse 1
  := by exists 1

-- Definition 51
structure Ring (X : Type) where
  plus : AbelianGroup X
  mul    : Monoid X
  dest_l : ∀ x : X, mul.op plus.e x = plus.e
  dest_r : ∀ x : X, mul.op x plus.e = plus.e
  dist_l : ∀ x y z : X,
    mul.op x (plus.op y z) = plus.op (mul.op x y) (mul.op x z)
  dist_r : ∀ y z x : X,
    mul.op (plus.op y z) x = plus.op (mul.op y x) (mul.op z x)

structure CommutativeRing (X : Type) where
  plus : AbelianGroup X
  mul    : CommutativeMonoid X
  dest_l : ∀ x : X, mul.op plus.e x = plus.e
  dest_r : ∀ x : X, mul.op x plus.e = plus.e
  dist_l : ∀ x y z : X,
    mul.op x (plus.op y z) = plus.op (mul.op x y) (mul.op x z)
  dist_r : ∀ y z x : X,
    mul.op (plus.op y z) x = plus.op (mul.op y x) (mul.op z x)

structure Field (X : Type) extends CommutativeRing X where
  CR : CommutativeRing X
  recipro : ∀ x : X, x ≠ CR.plus.e
    → ∃ y: X, monoid_inverse CR.mul.toMonoid x y
