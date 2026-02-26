import Proofs.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

----------------------------- Lecture 01 -----------------------------

-- Definition 7
def odd (j : ℤ) : Prop := ∃i, j = (2: ℤ) * i + (1: ℤ)

example : odd (7 : ℤ) := by
  dsimp [odd]
  exists 3

-- Proposition 8
theorem multiplying_odds_returns_odd :
  ∀ i j,
  odd i ∧ odd j → odd (i * j)
  := by intro i j h
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
theorem square_root_of_rational_is_rational :
∀ x,
  positive x ∧ rational √x → rational (x)
  := by introv h
        match h with
        | ⟨ hpos, hrat ⟩ =>
          dsimp [rational]
          obtain ⟨ p, q, hpq ⟩ := hrat
          use p^2, q^2
          rw [← Real.sq_sqrt (le_of_lt hpos)]
          simp [hpq]
          ring

-- Theorem 11
theorem transitive_implication :
  ∀ (p q r : Prop),
  (p → q) ∧ (q → r) → (p → r)
  := by intro p q r h
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

theorem parity_modulo_two :
  ∀ n : ℤ,
  (even n ↔ congruent_modulo n 0 2) ∧
  (odd  n ↔ congruent_modulo n 1 2)
  := by intro n
        dsimp [even, odd, congruent_modulo, divides]
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
theorem congruence_maintained_by_scaling :
  ∀ a b m : ℤ,
  congruent_modulo a b m ↔ ∀ n : ℤ, congruent_modulo (n*a) (n*b) m
  := by dsimp [congruent_modulo, divides]
        intro a b m
        constructor
        · intro h
          intro n
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
theorem divisible_by_6 :
  ∀ (n : ℤ),
  divides 6 n ↔ divides 2 n ∧ divides 3 n
  := by dsimp [divides]
        intro n
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
theorem difference_of_squares :
  ∀ n : ℤ,
  n > (0 : ℤ) → ∃ i j : ℤ, 4 * n = i^2 - j^2 ∧ natural i ∧ natural j
  := by intro n
        dsimp [natural]
        intro h
        exists (n+1), (n-1)
        constructor
        · linarith
        · constructor
          · linarith [h]
          · linarith [h]

-- Theorem 23
theorem transitivity_of_division :
  ∀ l m n : ℤ,
  divides l m ∧ divides m n → divides l n
  := by intro l m n
        dsimp [divides]
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

lemma transitivity_of_cong :
  ∀ {a b c n : ℤ},
  congruent_modulo a b n ∧ congruent_modulo b c n →
  congruent_modulo a c n
  := by intro a b c n
        dsimp [congruent_modulo, divides]
        intro h
        match h with
        | ⟨ hab, hbc ⟩ =>
           obtain ⟨ i, hi ⟩ := hab
           obtain ⟨ j, hj ⟩ := hbc
           exists (i + j)
           rw [mul_add, ← hi, ← hj]
           linarith

lemma symmetry_of_cong :
  ∀ {a b n : ℤ},
  congruent_modulo a b n → congruent_modulo b a n
  := by intro a b n
        dsimp [congruent_modulo, divides]
        intro h
        obtain ⟨ k, hk ⟩ := h
        exists -k
        linarith

theorem congruence_uniquely_characterises :
  ∀ m n : ℤ, m > 0 →
  ∀ x y : ℤ, P m n x ∧ P m n y → x = y
  := by intro m n h_m_pos x y hP
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
lemma choose_when_0_or_p :
  ∀ p m : ℕ, p > 0 →
  m = 0 ∨ m = p → congruent_modulo (Nat.choose p m) 1 p
  := by intro p m h_p_pos h_m_0_or_p
        dsimp [congruent_modulo, divides]
        cases h_m_0_or_p with
        | inl h_m_eq_0 => exists 0
                          simp [h_m_eq_0]
        | inr h_m_eq_p => exists 0
                          simp [h_m_eq_p]
