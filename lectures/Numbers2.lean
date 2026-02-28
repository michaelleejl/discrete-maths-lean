import Mathlib.Data.Nat.Basic
import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Nat.ModEq

import Mathlib.Tactic

open Nat

----------------------------- Lecture 05 -----------------------------

-- Theorem 53, Definition 54, Theorem 56
structure QuoRem (m n : ℕ) where
  q : ℕ
  r : ℕ
  eq : m = q * n + r
  lt : r < n

def division_algorithm : (m : ℕ) → (n: ℕ) → (n > 0) → QuoRem m n :=
  fun m => fun n => fun p =>
    if hle : m ≤ n then
      if hlt : m < n
        then
          have eq : m = 0 * n + m := by simp
          have lt : m < n := hlt
          ⟨ 0, m, eq, lt⟩
        else
          have heq : m = n := Nat.le_antisymm hle (Nat.not_lt.mp hlt)
          have eq : m = 1 * n + 0 := by simp [heq]
          have lt : 0 < n := p
          ⟨ 1 , 0, eq, lt ⟩
    else
      have h : n ≤ m := Nat.le_of_lt (Nat.gt_of_not_le hle)
      let ⟨ q, r, heq, hlt ⟩ := division_algorithm (m - n) n p;
      have eq : m = (q + 1) * n + r
        := calc
            m = (m - n) + n := by rw [Nat.sub_add_cancel h]
            _ = q * n + r + n := by rw [heq]
            _ = q * n + (r + n) := by rw [Nat.add_assoc]
            _ = q * n + (n + r) := by rw [Nat.add_comm r n]
            _ = (q * n + n) + r  := by rw [Nat.add_assoc]
            _ = (q + 1) * n + r := by rw [← Nat.succ_mul]
      ⟨q + 1, r, eq, hlt⟩

def quo : (m : ℕ) → (n : ℕ) → (n > 0) → ℕ :=
  fun m => fun n => fun p =>
    (division_algorithm m n p).q

def rem : (m : ℕ) → (n : ℕ) → (n > 0) → ℕ :=
  fun m => fun n => fun p =>
    (division_algorithm m n p).r

theorem division_theorem {m n : ℕ} :
    n > 0 → ∃!qr : ℕ × ℕ, qr.2 < n ∧ m = qr.1 * n + qr.2
  := by intro hpos
        let ⟨ q, r, eq, lt ⟩ := division_algorithm m n hpos
        refine ⟨(q, r), ?existence, ?uniqueness⟩
        · exact ⟨ lt, eq ⟩
        · intro ⟨ q', r' ⟩
          dsimp
          intro h
          match h with
          | ⟨ lt', eq' ⟩ =>
                have h1 : m - r  = n * q
                  := by rw [eq, Nat.add_sub_cancel, Nat.mul_comm]
                have h2 : m - r' = n * q'
                  := by rw [eq', Nat.add_sub_cancel, Nat.mul_comm]
                have h3 : r ≡ m [MOD n]
                  := by rw [Nat.modEq_iff_dvd]
                        exists q
                        linarith [h1]
                have h4 : r' ≡ m [MOD n]
                  := by rw [Nat.modEq_iff_dvd]
                        exists q'
                        linarith [h2]
                have h5 : r' ≡ r [MOD n]
                  := Nat.ModEq.trans h4 (Nat.ModEq.symm h3)
                have h6 : r' = r
                  := Nat.ModEq.eq_of_lt_of_lt h5 lt' lt
                have h7 : q' = q
                  := by rw [h6] at eq'
                        rw [eq'] at eq
                        rw [Nat.add_left_inj] at eq
                        rw [Nat.mul_left_inj (Nat.ne_of_gt hpos)] at eq
                        exact eq
                apply Prod.ext
                · exact h7
                · exact h6
