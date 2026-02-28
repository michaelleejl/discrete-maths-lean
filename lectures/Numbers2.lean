import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq

import Mathlib.Logic.ExistsUnique

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

-- Proposition 57
theorem cong_mod_iff_rem_eq {k l m : ℕ} (h_pos : m > 0) :
    k ≡ l [MOD m] ↔ rem k m h_pos = rem l m h_pos
  := by constructor
        · intro hcong
          dsimp [rem]
          let ⟨q, r, eq, lt⟩ := division_algorithm k m h_pos
          let ⟨q', r', eq', lt'⟩ := division_algorithm l m h_pos
          have h1 : k - r  = m * q
                  := by rw [eq, Nat.add_sub_cancel, Nat.mul_comm]
          have h2 : l - r' = m * q'
            := by rw [eq', Nat.add_sub_cancel, Nat.mul_comm]
          have h3: r ≡ k [MOD m]
            := by rw [Nat.modEq_iff_dvd]
                  exists q
                  linarith [h1]
          have h4: r' ≡ l [MOD m]
            := by rw [Nat.modEq_iff_dvd]
                  exists q'
                  linarith [h2]
          have h5: r ≡ l [MOD m]
            := Nat.ModEq.trans h3 hcong
          have h6: r ≡ r' [MOD m]
            := Nat.ModEq.trans h5 (Nat.ModEq.symm h4)
          have h7: r = r' := Nat.ModEq.eq_of_lt_of_lt h6 lt lt'
          exact h7
        · intro heq
          dsimp [rem] at heq
          let divk := division_algorithm k m h_pos
          let divl := division_algorithm l m h_pos
          have h_rw : (l: ℤ) - (k: ℤ) = ((divl.q - divk.q) : ℤ) * m
            := calc
                (l : ℤ) - (k : ℤ) = divl.q * m + divl.r - divk.r - divk.q * m
                  := by simp [divk.eq, divl.eq]
                        linarith
                _ = (divl.q - divk.q) * m
                  := by rw [heq]
                        linarith
          have h_div : (m : ℤ) ∣ (l: ℤ) - (k: ℤ)
            := by exists (divl.q - divk.q)
                  rw [h_rw]
                  linarith
          exact Nat.modEq_of_dvd h_div

-- Corollary 58
lemma rem_is_identity_when_mltn {m n : ℕ} (h_pos : n > 0) :
    (m < n) → rem m n h_pos = m
  := by intro hnsmall
        dsimp [rem]
        let w := (0, m)
        have p : w.2 < n ∧ m = w.1 * n + w.2
          := by dsimp [w]
                constructor
                · exact hnsmall
                · simp
        let ⟨ q, r, eq, lt ⟩ := division_algorithm m n h_pos
        let w' := (q, r)
        have p' : w'.2 < n ∧ m = w'.1 * n + w'.2
          := by dsimp [w']
                constructor
                · exact lt
                · exact eq
        have heu : ∃!qr : ℕ × ℕ, qr.2 < n ∧ m = qr.1 * n + qr.2
          := division_theorem h_pos
        have heq : (0, m) = (q, r)
         := heu.unique p p'
        exact (Prod.mk.inj heq).2.symm

theorem modulo_arithmetic_nat {m n : ℕ} (h_pos : n > 0) :
    m ≡ rem m n h_pos [MOD n]
  := by dsimp [rem]
        rw [cong_mod_iff_rem_eq h_pos]
        let d := division_algorithm m n h_pos
        rw [rem_is_identity_when_mltn h_pos d.lt]
        dsimp [rem]

theorem modulo_arithmetic_int {n k : ℤ} (h_pos : n > 0) :
    ∃! knorm, k ≡ knorm [ZMOD n] ∧ 0 ≤ knorm ∧ knorm < n
  := suffices
      h_k_nonneg : ∀ j, j ≥ 0 →
        ∃! jnorm, j ≡ jnorm [ZMOD n] ∧ 0 ≤ jnorm ∧ jnorm < n
      by by_cases h: k ≥ 0
         · specialize h_k_nonneg k
           exact h_k_nonneg h
         · have hmod : k ≡ k - n * k [ZMOD n]
              := by rw [Int.modEq_sub_modulus_mul_iff]
           have hminusn : (1 - n) ≤ 0
              := by linarith [h_pos]
           have hminusk : k ≤ 0
              := by linarith [h]
           have hnonneg : k - n * k ≥ 0
              := calc
                 k - n * k = k - k * n   := by rw [Int.mul_comm]
                         _ = k*1 - k*n   := by rw [Int.mul_one]
                         _ = k * (1 - n) := by rw [← Int.mul_sub]
                         _ ≥ 0
                          := Int.mul_nonneg_of_nonpos_of_nonpos hminusk hminusn
           specialize h_k_nonneg (k - n * k)
           have hknorm := h_k_nonneg hnonneg
           rcases hknorm with ⟨knorm, ⟨hknormmod, hknombounds⟩, huniq⟩
           exists knorm
           dsimp
           constructor
           · constructor
             · exact hmod.trans hknormmod
             · exact hknombounds
           · intro y ⟨hymod, hybounds⟩
             have hyeq : k - n * k ≡ y [ZMOD n]
                := hmod.symm.trans hymod
             exact huniq y ⟨hyeq, hybounds⟩
      by intro j hj
         let jn := j.toNat
         let h_jn : jn = j := Int.toNat_of_nonneg hj
         let nn := n.toNat
         have h_nn : nn = n := Int.toNat_of_nonneg (Int.le_of_lt h_pos)
         have h_nn_pos : nn > 0 := by rw [← h_nn] at h_pos
                                      linarith
         let d := division_algorithm jn nn h_nn_pos
         have h_eq : jn ≡ d.r [MOD nn]
           := modulo_arithmetic_nat h_nn_pos
         exists rem jn nn h_nn_pos
         dsimp
         constructor
         · constructor
           · rw [← h_jn, ← h_nn]
             exact Int.natCast_modEq_iff.mpr h_eq
           · constructor
             · linarith [d.r.zero_le]
             · dsimp [rem]
               linarith [d.lt]
         · intro y ⟨hymod, hyzero, hylt⟩
           let yn := y.toNat
           let h_yn : yn = y := Int.toNat_of_nonneg hyzero
           rw [← h_yn]
           have hynlt : yn < nn
            := Int.ofNat_lt.mp (by rw [← h_yn, ← h_nn] at hylt
                                   exact hylt)
           rw [Nat.cast_inj]
           have h_y_eq : rem yn nn h_nn_pos = yn
            := rem_is_identity_when_mltn h_nn_pos hynlt
           rw [← h_y_eq, ← cong_mod_iff_rem_eq h_nn_pos]
           have h_cong : yn ≡ jn [MOD nn]
            := by rw [← h_jn, ← h_yn, ← h_nn] at hymod
                  exact (Int.natCast_modEq_iff.mp hymod).symm
           exact h_cong
