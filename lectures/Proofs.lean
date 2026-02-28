import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Int.NatPrime
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring


open Nat
----------------------------- Lecture 01 -----------------------------

-- Definition 7
def odd (j : ℤ) : Prop := ∃i, j = (2: ℤ) * i + (1: ℤ)

example : odd (7 : ℤ) := by
  dsimp [odd]
  exists 3

-- Proposition 8
theorem multiplying_odds_returns_odd {i j} :
    odd i ∧ odd j → odd (i * j)
  := by intro h
        match h with
        | ⟨ hi, hj ⟩ =>
            dsimp [odd]
            obtain ⟨ a, ha ⟩ := hi
            obtain ⟨ b, hb ⟩ := hj
            use (2*a*b + a + b)
            simp [ha, hb]
            ring

-- Definition 9a
def rational (x : ℝ) : Prop := ∃ (p q : ℤ), x = (p : ℝ) / (q : ℝ)
def irrational (x : ℝ) : Prop := ¬ rational x

-- Definition 9bi
def positive (x : ℝ) : Prop := x > (0 : ℝ)

-- Definition 9bii
def negative (x : ℝ) : Prop := x < (0 : ℝ)

-- Definition 9ci
def nonnegative (x : ℝ) : Prop := x >= (0 : ℝ)

-- Definition 9cii
def nonpositive (x : ℝ) : Prop := x <= (0 : ℝ)

-- Definition 9b
def natural (x : ℤ) : Prop := x >= (0 : ℤ)

-- Proposition 10
theorem square_root_of_rational_is_rational {x : ℝ} :
    positive x → rational √x → rational (x)
  := by introv hpos hrat
        dsimp [rational]
        obtain ⟨ p, q, hpq ⟩ := hrat
        use p^2, q^2
        rw [← Real.sq_sqrt (le_of_lt hpos)]
        simp [hpq]
        ring

-- Theorem 11
theorem transitive_implication {p q r : Prop} :
    (p → q) ∧ (q → r) → (p → r)
  := by intro h
        match h with
        | ⟨ hpq, hqr ⟩ =>
          intro p
          have q := hpq p
          have r := hqr q
          exact r

----------------------------- Lecture 02 -----------------------------

-- Definition 12
def divides (d n : ℤ) : Prop := ∃ k, n = d * k

-- Example 13
example : divides (2 : ℤ) (4 : ℤ) := by
  dsimp [divides]
  exists 2

-- Definition 14
def congruent_modulo (a b m : ℤ) : Prop := divides m (a - b)

-- Example 15
example : congruent_modulo (18 : ℤ) (2 : ℤ) (4 : ℤ) := by
  dsimp [congruent_modulo, divides]
  exists 4

-- Proposition 16
def even (j : ℤ) : Prop := ∃ i, j = (2 : ℤ) * i

theorem parity_modulo_two {n : ℤ} :
    (even n ↔ congruent_modulo n 0 2) ∧
    (odd  n ↔ congruent_modulo n 1 2)
  := by dsimp [even, odd, congruent_modulo, divides]
        constructor
        · constructor
          · intro heven
            obtain ⟨i, hn⟩ := heven
            exists i
            simp [hn]
          · intro hcong0
            obtain ⟨k, hn⟩ := hcong0
            simp at hn
            exists k
        · constructor
          · intro hodd
            obtain ⟨i, hn⟩ := hodd
            use i
            simp [hn]
          · intro hcong1
            obtain ⟨k, hn⟩ := hcong1
            use k
            linarith

-- Proposition 18
theorem congruence_maintained_by_scaling {a b m : ℤ} :
    congruent_modulo a b m ↔ ∀ n : ℤ, congruent_modulo (n*a) (n*b) m
  := by dsimp [congruent_modulo, divides]
        constructor
        · intro h n
          obtain ⟨ i, hab ⟩ := h
          exists n * i
          rw [← Int.mul_sub, hab]
          linarith
        · intro h
          specialize h (1 : ℤ)
          repeat rw [Int.one_mul] at h
          exact h

----------------------------- Lecture 03 -----------------------------

-- Theorem 19
theorem divisible_by_6 {n : ℤ} :
    divides 6 n ↔ divides 2 n ∧ divides 3 n
  := by dsimp [divides]
        constructor
        · intro hdiv6
          obtain ⟨ k, hk ⟩ := hdiv6
          constructor
          · exists 3 * k
            linarith
          · exists 2 * k
            linarith
        · intro hdivs
          match hdivs with
          | ⟨ hdiv2, hdiv3 ⟩ =>
            obtain ⟨ i, hi ⟩ := hdiv2
            obtain ⟨ j, hj ⟩ := hdiv3
            exists (i - j)
            linarith

-- Proposition 21
theorem difference_of_squares {n : ℤ} :
    n > (0 : ℤ) → ∃ i j : ℤ, 4 * n = i^2 - j^2 ∧ natural i ∧ natural j
  := by dsimp [natural]
        intro h
        exists (n+1), (n-1)
        constructor
        · linarith
        · constructor
          · linarith [h]
          · linarith [h]

-- Theorem 23
theorem transitivity_of_division {l m n : ℤ} :
    divides l m ∧ divides m n → divides l n
  := by dsimp [divides]
        intro h
        match h with
          | ⟨ hlm, hmn ⟩ =>
              obtain ⟨i, hi⟩ := hlm
              obtain ⟨j, hj⟩ := hmn
              use i * j
              rw [hj, hi, mul_assoc]

----------------------------- Lecture 04 -----------------------------

-- Proposition 24
def P (m n z : ℤ) : Prop := 0 ≤ z ∧ z < m ∧ congruent_modulo z n m

lemma transitivity_of_cong {a b c n : ℤ} :
    congruent_modulo a b n ∧ congruent_modulo b c n →
    congruent_modulo a c n
  := by dsimp [congruent_modulo, divides]
        intro h
        match h with
        | ⟨ hab, hbc ⟩ =>
           obtain ⟨ i, hi ⟩ := hab
           obtain ⟨ j, hj ⟩ := hbc
           exists (i + j)
           rw [mul_add, ← hi, ← hj]
           linarith

lemma symmetry_of_cong {a b n : ℤ} :
    congruent_modulo a b n → congruent_modulo b a n
  := by dsimp [congruent_modulo, divides]
        intro h
        obtain ⟨ k, hk ⟩ := h
        exists -k
        linarith

theorem congruence_uniquely_characterises {m n : ℤ} :
    m > 0 →
    ∀ x y : ℤ, P m n x ∧ P m n y → x = y
  := by intro h_m_pos x y hP
        dsimp [P] at hP
        match hP with
        | ⟨ ⟨ xgteq0, xltm, hx ⟩, ⟨ ygteq0, yltm, hy ⟩ ⟩ =>
          have hxy : congruent_modulo x y m
            := transitivity_of_cong ⟨ hx , symmetry_of_cong hy ⟩
          dsimp [congruent_modulo, divides] at hxy
          obtain ⟨ i, hi ⟩ := hxy
          have ⟨ hboundl, hboundr ⟩ : m * -1 < x - y ∧ x - y < m * 1
            := by constructor <;> linarith
          have ibound : - 1 < i ∧ i < 1
            := by constructor
                  · rw [hi, Int.mul_lt_mul_left h_m_pos] at hboundl
                    exact hboundl
                  · rw [hi, Int.mul_lt_mul_left h_m_pos] at hboundr
                    exact hboundr
          have ieq0 : i = 0 := by linarith
          rw [← sub_eq_zero, hi, ieq0]
          linarith

-- Proposition 25
theorem squares_mod_4 :
  ∀ (n : ℤ),
  congruent_modulo (n^2) 0 4 ∨ congruent_modulo (n^2) 1 4
  := by intro n
        dsimp [congruent_modulo, divides]
        cases (Int.even_or_odd n) with
        | inl heven => dsimp [Even] at heven
                       obtain ⟨ i , hi ⟩ := heven
                       left
                       use i^2
                       simp [hi]
                       linarith
        | inr hodd => dsimp [Odd] at hodd
                      obtain ⟨ j, hj ⟩ := hodd
                      right
                      use j^2 + j
                      simp [hj]
                      linarith

-- Lemma 27
lemma choose_when_0_or_p {p m : ℕ} :
  p > 0 →
  m = 0 ∨ m = p → (p.choose m) ≡ 1 [MOD p]
  := by intro h_p_pos h_m_0_or_p
        rw [Nat.modEq_iff_dvd]
        cases h_m_0_or_p with
        | inl h_m_eq_0 => exists 0
                          simp [h_m_eq_0]
        | inr h_m_eq_p => exists 0
                          simp [h_m_eq_p]


-- Lemma 28
theorem classical_or :
  ∀ {a b : Prop},
  (a ∨ b) → ¬ b → a
    := by intro a b hab hna
          cases hab with
          | inl ha => exact ha
          | inr hb => contradiction


lemma h_choose_rw {p m : ℕ} :
   m ≤ p → (p)! = (p.choose m) * ((m)! * (p - m)!)
  :=  by intro hle
         have h_dvd :
          (m)! * (p-m)! ∣ (p)!
          := Nat.factorial_mul_factorial_dvd_factorial hle
         calc
          (p)! = (p.choose m) * ((m)! * (p - m)!)
            := by rw [Nat.choose_eq_factorial_div_factorial hle]
                  rw [Nat.div_mul_cancel h_dvd]

lemma extract_p_from_p! {p m : ℕ} :
    Nat.Prime p →
    (p)! = (p.choose m) * ((m)! * (p - m)!) →
    p*(p-1)! = (p.choose m) * ((m)! * (p - m)!)
  := by intro h_prime h_eq
        have h_succ : ∃ k, p = k + 1
          := by exact Nat.exists_eq_succ_of_ne_zero h_prime.ne_zero
        obtain ⟨ k, hk ⟩ := h_succ
        have h_pred : k = p - 1
          := by simp [hk]
        rw [hk, Nat.factorial_succ, ← hk, h_pred] at h_eq
        exact h_eq

lemma num_does_not_divide_smaller {a b : ℕ} :
    0 < a → a < b → ¬ (b ∣ a)
  := by intros h_pos h_lt
        intro h_div
        obtain ⟨k, hk⟩ := h_div
        have h_k_pos : 0 < k
          := Nat.pos_of_ne_zero (by intro hk0
                                    rw [hk0, mul_zero] at hk
                                    exact h_pos.ne (symm hk))
        have h_ge : a ≥ b
          := by rw [hk]
                exact Nat.le_mul_of_pos_right b h_k_pos
        have contra : ¬ (a < b)
          := Nat.not_lt_of_ge h_ge
        contradiction

lemma euclid_contrapositive {p a b : ℕ} :
    Nat.Prime p → ¬ (p ∣ a) ∧ ¬ (p ∣ b) → ¬ (p ∣ a * b)
  := by intro h_prime ⟨ h_na, h_nb ⟩
        by_contra h_div
        have h_p : p ∣ a ∨ p ∣ b
          := by rw [← h_prime.dvd_mul]
                exact h_div
        cases h_p with
          | inl h_a => contradiction
          | inr h_b => contradiction

lemma p_does_not_divide_fact {p m : ℕ} :
    Nat.Prime p → m < p → ¬ (p ∣ (m)!)
  := by intro h_prime h_lt
        induction m with
        | zero      => simp [h_prime.ne_one]
        | succ n ih => rw [Nat.factorial_succ]
                       apply euclid_contrapositive h_prime
                       constructor
                       · have h_s_pos : 0 < n+1
                            := Nat.succ_pos n
                         exact num_does_not_divide_smaller
                            h_s_pos h_lt
                       · have h_small : n < p
                            := Nat.lt_of_succ_lt h_lt
                         exact ih h_small

lemma choose_when_prime_exclusive {p m : ℕ} :
  Nat.Prime p → 0 < m ∧ m < p → (p.choose m) ≡ 0 [MOD p]
  := by intro h_prime ⟨hml, hmu⟩
        have hle : m ≤ p
          := Nat.le_of_lt hmu
        have h_eq : (p)! = (p.choose m) * ((m)! * (p - m)!)
          := h_choose_rw hle
        have h_extracted : p*(p-1)! = (p.choose m) * ((m)! * (p - m)!)
          := extract_p_from_p! h_prime h_eq
        have h_p_div : p ∣ (p.choose m) * ((m)! * (p - m)!)
          := by use Nat.factorial (p-1)
                simp [h_extracted]
        have h_p_div_or : (p ∣ (p.choose m)) ∨ (p ∣ ((m)! * (p - m)!))
          := by rw [h_prime.dvd_mul] at h_p_div
                exact h_p_div
        have h_p_ndiv_1 : ¬ (p ∣ (m)!)
          := p_does_not_divide_fact h_prime hmu
        have h_p_ndiv_2 : ¬ (p ∣ (p - m)!)
          := have h_small : p - m < p
                := Nat.sub_lt (h_prime.pos) (hml)
             p_does_not_divide_fact h_prime h_small
        have h_p_ndiv : ¬ (p ∣ (m)! * (p - m)!)
          := euclid_contrapositive h_prime ⟨ h_p_ndiv_1, h_p_ndiv_2 ⟩
        have h_divides : p ∣ (p.choose m)
          := classical_or h_p_div_or h_p_ndiv
        rw [Nat.dvd_iff_mod_eq_zero] at h_divides
        exact h_divides

-- Proposition 29
theorem choose_when_prime_inclusive {p m : ℕ} :
    Nat.Prime p → 0 ≤ m ∧ m ≤ p →
    (p.choose m) ≡ 0 [MOD p] ∨ (p.choose m) ≡ 1 [MOD p]
  := by intro h_prime ⟨ hlb, hub ⟩
        have h_p_pos := h_prime.pos
        rw [Nat.le_iff_lt_or_eq] at hlb
        rw [Nat.le_iff_lt_or_eq] at hub
        cases hlb with
        | inl h_m_gt_0 =>
          cases hub with
          | inl h_p_gt_m
            => left
               exact choose_when_prime_exclusive
                  h_prime
                  ⟨h_m_gt_0, h_p_gt_m⟩
          | inr h_p_eq_m
            => right
               exact choose_when_0_or_p h_p_pos (Or.inr (h_p_eq_m))
        | inr h_m_eq_0
            => right
               exact choose_when_0_or_p
                  h_p_pos
                  (Or.inl (symm h_m_eq_0))

-- Corollary 33
theorem the_freshmans_dream {m n p : ℕ} :
  Nat.Prime p → (m + n)^p ≡ m^p + n^p [MOD p]
  := by intro h_prime
        simp only [add_pow, Finset.sum_range_succ']
        have h_succ : ∃ k, p = k + 1
          := Nat.exists_eq_succ_of_ne_zero h_prime.ne_zero
        have h_p_ge_1 : p ≥ 1
          := h_prime.pos
        obtain ⟨ i , hi ⟩ := h_succ
        rw [hi]
        have h_pred : i = p - 1
          := by simp [hi]
        rw [Finset.sum_range_succ, h_pred,
            Nat.sub_add_cancel h_prime.pos]
        conv =>
          lhs
          simp
        have h_each : ∀ k ∈ Finset.range (p - 1),
                      p ∣ m^(k+1) * n^(p-(k+1)) * p.choose (k+1)
            := by intro k hk
                  suffices h_div : p ∣ p.choose (k+1)
                    by rw [mul_comm]
                       apply Nat.dvd_mul_right_of_dvd
                       exact h_div
                  rw [Nat.dvd_iff_mod_eq_zero]
                  rw [Finset.mem_range] at hk
                  have hkl : 0 < k+1 := by linarith
                  have hku : k + 1 < p := by linarith
                  exact choose_when_prime_exclusive
                      h_prime ⟨ hkl, hku ⟩
        have h_zero : p ∣ ∑ k ∈ Finset.range (p - 1),
                      m^(k+1) * n^(p-(k+1)) * p.choose (k+1)
          := Finset.dvd_sum h_each
        rw [← zero_add (m^p + n^p), add_assoc]
        rw [Nat.dvd_iff_mod_eq_zero] at h_zero
        exact ModEq.add h_zero (ModEq.refl (m^p + n^p))

-- Corollary 34
theorem the_dropout_lemma {m p : ℕ} :
    Nat.Prime p → (m + 1)^p ≡ m^p + 1 [MOD p]
  := by intro h
        have h_fr : (m + 1)^p ≡ m^p + 1^p [MOD p]
          := the_freshmans_dream h
        rw [Nat.one_pow] at h_fr
        exact h_fr

-- Corollary 35
theorem the_many_dropout_lemma {m p : ℕ} :
    Nat.Prime p → (m + i)^p ≡ m^p + i [MOD p]
  := by intro h
        induction i with
        | zero      => rw [Nat.add_zero]
                       exact ModEq.refl (m^p)
        | succ n ih => rw [← Nat.add_assoc]
                       have h_d : (m + n + 1)^ p ≡ (m+n)^p + 1 [MOD p]
                         := the_dropout_lemma h
                       have h_i : (m+n)^p + 1 ≡ m^p + n + 1 [MOD p]
                         := ModEq.add_right 1 ih
                       exact ModEq.trans h_d h_i

----------------------------- Lecture 05 -----------------------------

theorem double_negation_elim {p : Prop} :
    ¬ ¬ p ↔ p
  := by constructor
        · intro h
          by_contra hn
          exact h hn
        · intro h
          by_contra hn
          exact hn h

-- Theorem 37
theorem contraposition {p q : Prop} :
    (p → q) ↔ (¬ q → ¬ p)
  := by constructor
        · intro h hnq
          by_contra hp
          have hq: q := h hp
          exact hnq hq
        · intro h hp
          by_contra hnq
          have hnp : ¬p := h hnq
          exact hnp hp

-- Corollary 41
theorem square_root_irrational {x : ℝ} :
    positive x → irrational x → irrational (√x)
  := by dsimp [irrational]
        intro h_pos
        rw [contraposition, double_negation_elim,
            double_negation_elim]
        exact square_root_of_rational_is_rational h_pos

-- Lemma 42
structure State (x : ℝ) (a₀ b₀ n : ℕ) where
  ps : ℕ
  a  : ℕ
  b  : ℕ
  hpos_a : 0 < a
  hpos_b : 0 < b
  hfrac  : x = (a : ℝ) / (b : ℝ)
  heq : ps * a = a₀
  hge : 2^n ≤ ps

noncomputable def a_seq
    (a₀ b₀ : ℕ)
    (hpos_a₀ : 0 < a₀) (hpos_b₀ : 0 < b₀)
    (hfrac₀ : x = (a₀ : ℝ) / (b₀ : ℝ))
    (h_c : ∀ m n : ℕ, 0 < m → 0 < n → x = m / n → ∃ p : ℕ, Nat.Prime p ∧ p ∣ m ∧ p ∣ n)
    : (n : ℕ) → State x a₀ b₀ n
    | 0 =>  have h_eq : 1 * a₀ = a₀ := by simp
            have h_gt : 1 ≥ 2^0 := by rfl
            ⟨1, a₀, b₀, hpos_a₀, hpos_b₀, hfrac₀, h_eq, h_gt⟩
    | n+1 => let ⟨ ps, an, bn, hpos_an, hpos_bn, hfracn, heqn, hgen ⟩
                := a_seq a₀ b₀ hpos_a₀ hpos_b₀ hfrac₀ h_c n;
             let p := Classical.choose (h_c an bn hpos_an hpos_bn hfracn)
             let ⟨p_prime, ⟨p_div_a, p_div_b⟩⟩
              := Classical.choose_spec (h_c an bn hpos_an hpos_bn hfracn)
             let a_new : ℕ := an / p
             let b_new : ℕ := bn / p
             have hpos_an : (0 < a_new)
              := Nat.div_pos (Nat.le_of_dvd hpos_an p_div_a) (Nat.Prime.pos p_prime)
             have hpos_bn : (0 < b_new)
              := Nat.div_pos (Nat.le_of_dvd hpos_bn p_div_b) (Nat.Prime.pos p_prime)
             have hp : 1 <= p
              := Nat.one_le_of_lt (Nat.pos_of_ne_zero p_prime.ne_zero)
             have hfrac_new : x = a_new / ((b_new) : ℝ)
              := calc
                  x = an / bn := hfracn
                  _ = ((p * a_new) : ℕ) / ((p * b_new) : ℕ)
                    := by rw [Nat.mul_div_cancel' p_div_b,
                              Nat.mul_div_cancel' p_div_a]
                  _ = ((p * a_new)) / ((p * b_new))
                    := by simp
                  _ = (a_new) / (b_new)
                    := by field_simp
             have heq_new : ps*p*a_new = a₀
              := by dsimp [a_new]
                    rw [Nat.mul_assoc, Nat.mul_div_cancel' p_div_a]
                    exact heqn
             have hge_new : 2^(n+1) ≤ ps*p
                :=
                    suffices h_obj : 2^n ≤ ps ∧ 2 ≤ p
                    by match h_obj with
                        | ⟨ h_ps, h_p ⟩ =>
                            calc
                              2^(n+1) = 2^n * 2 := by rw [pow_succ]
                              _       ≤ ps * p := Nat.mul_le_mul h_ps h_p
                    ⟨hgen, p_prime.two_le⟩
             ⟨ps*p, a_new, b_new, hpos_an, hpos_bn, hfrac_new, heq_new, hge_new⟩

lemma rational_normal_form {x : ℝ} :
    x > 0 →
      ((∃ a b : ℕ, 0 < a ∧ 0 < b ∧ x = a/b) ↔
      (∃ m n : ℕ, 0 < m ∧ 0 < n ∧
        x = m/n ∧ ¬ (∃ p: ℕ, Nat.Prime (p) ∧ p ∣ m ∧ p ∣ n)))
  := by intros h
        constructor
        · intro h_rat
          obtain ⟨ a, b, ha, hb, hx ⟩ := h_rat
          by_contra h_c
          repeat push_neg at h_c
          let a_contra := a_seq a b ha hb hx h_c a
          have h_a_seq_eq_a : (a_contra.ps * a_contra.a = a)
            := a_contra.heq
          have h_a_seq_ge : (2^a ≤ a_contra.ps)
            := a_contra.hge
          have h_a_seq_gt : (2^a ≤ a)
            := calc
                2^a ≤ a_contra.ps := h_a_seq_ge
                _ ≤ a_contra.ps * a_contra.a
                  := Nat.le_mul_of_pos_right a_contra.ps a_contra.hpos_a
                _ = a := h_a_seq_eq_a
          have hpn : ¬ (a < 2^a) := Nat.not_lt_of_ge h_a_seq_gt
          have hp : a < 2^a := Nat.lt_two_pow_self
          contradiction
        · intro h_rat_norm
          obtain ⟨ a, b, _, _, hx, _ ⟩:= h_rat_norm
          exists a, b
