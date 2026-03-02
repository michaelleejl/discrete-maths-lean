import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic

import Mathlib.Logic.ExistsUnique

import Mathlib.Tactic


open Nat

----------------------------- Lecture 06 -----------------------------

-- Theorem 53, Definition 54, Theorem 56
structure QuoRem (m n : ℤ) where
  q : ℤ
  r : ℤ
  eq : m = q * n + r
  lt : r < n
  qnat : q >= 0
  rnat : r >= 0

def division_algorithm : (m : ℤ) → (n: ℤ) → (m ≥ 0) → (n > 0) → QuoRem m n :=
  fun m => fun n => fun pm => fun pn =>
    if hle : m ≤ n then
      if hlt : m < n
        then
          have eq : m = 0 * n + m := by simp
          have lt : m < n := hlt
          have obv : (0: ℤ) ≥ 0 := by rfl
          ⟨ 0, m, eq, lt, obv, pm⟩
        else
          have heq : m = n := Int.le_antisymm hle (Int.not_lt.mp hlt)
          have eq : m = 1 * n + 0 := by simp [heq]
          have lt : 0 < n := pn
          have obv0 : (0: ℤ) ≥ 0 := by rfl
          have obv1 : (1: ℤ) ≥ 0 := by linarith
          ⟨ 1 , 0, eq, lt, obv1, obv0⟩
    else
      have h : m-n ≥ 0 := by linarith
      let ⟨ q, r, heq, hlt, hqnat, hrnat ⟩
        := division_algorithm (m - n) n h pn;
      have eq : m = (q + 1) * n + r
        := by linarith
      have hq : q+1 ≥ 0 := by linarith
      ⟨q + 1, r, eq, hlt, hq, hrnat⟩
  termination_by m n _ _ => m.toNat

def quo : (m : ℤ) → (n : ℤ) → (m ≥ 0) → (n > 0) → ℤ :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).q

def rem : (m : ℤ) → (n : ℤ) → (m ≥ 0) → (n > 0) → ℤ :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).r

def rem_nonneg : (m : ℤ) → (n : ℤ) → (hm : m ≥ 0) → (hn : n > 0) →
                  0 ≤ (rem m n hm hn) :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).rnat

theorem division_theorem {m n : ℤ} (hmnonneg : m ≥ 0) (hnpos : n > 0) :
    ∃!qr : ℤ × ℤ, qr.1 ≥ 0 ∧ qr.2 ≥ 0 ∧ qr.2 < n ∧ m = qr.1 * n + qr.2
  := by
        let ⟨ q, r, eq, lt, hq, hr ⟩
          := division_algorithm m n hmnonneg hnpos;
        refine ⟨(q, r), ?existence, ?uniqueness⟩
        · exact ⟨ hq, hr, lt, eq ⟩
        · intro ⟨ q', r' ⟩
          dsimp
          intro h
          match h with
          | ⟨ hq', hr', lt', eq' ⟩ =>
                have h1 : m - r  = n * q
                  := by linarith
                have h2 : m - r' = n * q'
                  := by linarith
                have h3 : r ≡ m [ZMOD n]
                  := by rw [Int.modEq_iff_dvd]
                        exists q
                have h4 : r' ≡ m [ZMOD n]
                  := by rw [Int.modEq_iff_dvd]
                        exists q'
                have h5 : r' ≡ r [ZMOD n]
                  := h4.trans (h3.symm)
                have h6 : r' = r := by
                  have heq := Int.ModEq.eq h5
                  rw [Int.emod_eq_of_lt hr lt,
                      Int.emod_eq_of_lt hr' lt'] at heq
                  exact heq
                have h7 : q' = q
                  := by rw [h6] at eq'
                        rw [eq'] at eq
                        rw [Int.add_left_inj] at eq
                        exact mul_right_cancel₀ (Int.ne_of_gt hnpos) eq
                apply Prod.ext
                · exact h7
                · exact h6

-- Proposition 57
theorem cong_mod_iff_rem_eq {k l m : ℤ}
    (hknonneg : k ≥ 0) (hlnonneg : l ≥ 0) (hmpos : m > 0) :
    k ≡ l [ZMOD m] ↔ rem k m hknonneg hmpos = rem l m hlnonneg hmpos
  := by constructor
        · intro hcong
          dsimp [rem]
          let ⟨q, r, eq, lt, hq, hr⟩
            := division_algorithm k m hknonneg hmpos
          let ⟨q', r', eq', lt', hq', hr'⟩
              := division_algorithm l m hlnonneg hmpos
          have h1 : k - r  = m * q
              := by linarith
          have h2 : l - r' = m * q'
              := by linarith
          have h3: r ≡ k [ZMOD m]
            := by rw [Int.modEq_iff_dvd]
                  exists q
          have h4: r' ≡ l [ZMOD m]
            := by rw [Int.modEq_iff_dvd]
                  exists q'
          have h5: r ≡ l [ZMOD m]
            := h3.trans hcong
          have h6: r ≡ r' [ZMOD m]
            := h5.trans (h4.symm)
          have h7: r = r'
            := by have heq := Int.ModEq.eq h6
                  rw [Int.emod_eq_of_lt hr lt,
                      Int.emod_eq_of_lt hr' lt',] at heq
                  exact heq
          exact h7
        · intro heq
          dsimp [rem] at heq
          let divk := division_algorithm k m hknonneg hmpos
          let divl := division_algorithm l m hlnonneg hmpos
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
          exact Int.modEq_of_dvd h_div

-- Corollary 58
lemma rem_is_identity_when_mltn {m n : ℤ}
    (hmnonneg : m ≥ 0) (hnpos : n > 0) :
    (m < n) → rem m n hmnonneg hnpos = m
  := by intro hnsmall
        dsimp [rem]
        let w := ((0 : ℤ) , m)
        have p :  w.1 ≥ 0 ∧ w.2 ≥ 0 ∧  w.2 < n ∧ m = w.1 * n + w.2
          := by dsimp [w]
                constructor
                · trivial
                · constructor
                  · exact hmnonneg
                  · constructor
                    · exact hnsmall
                    · simp
        let ⟨ q, r, eq, lt, hq, hr ⟩
          := division_algorithm m n hmnonneg hnpos
        let w' := (q, r)
        have p' : w'.1 ≥ 0 ∧ w'.2 ≥ 0 ∧ w'.2 < n ∧ m = w'.1 * n + w'.2
          := by dsimp [w']
                constructor
                · trivial
                · constructor
                  · exact hr
                  · constructor
                    · exact lt
                    · exact eq
        have heu : ∃!qr : ℤ × ℤ, qr.1 ≥ 0 ∧ qr.2 ≥ 0 ∧ qr.2 < n ∧ m = qr.1 * n + qr.2
          := division_theorem hmnonneg hnpos;
        have heq : (0, m) = (q, r)
         := heu.unique p p'
        exact (Prod.mk.inj heq).2.symm

theorem modulo_arithmetic_nat {m n : ℤ}
    (hmnonneg : m ≥ 0) (hnpos : n > 0) :
    m ≡ rem m n hmnonneg hnpos [ZMOD n]
  := by dsimp [rem]
        let d := division_algorithm m n hmnonneg hnpos
        rw [cong_mod_iff_rem_eq hmnonneg d.rnat hnpos]
        rw [rem_is_identity_when_mltn d.rnat hnpos d.lt]
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
         let d := division_algorithm j n hj h_pos
         have h_eq : j ≡ d.r [ZMOD n]
           := modulo_arithmetic_nat hj h_pos
         exists d.r
         dsimp
         constructor
         · constructor
           · exact h_eq
           · constructor
             · exact d.rnat
             · dsimp [rem]
               linarith [d.lt]
         · intro y ⟨hymod, hyzero, hylt⟩
           have hcong : y ≡ d.r [ZMOD n]
            := hymod.symm.trans h_eq
           let d' := division_algorithm y n hyzero h_pos
           have hyrem : y = d'.r
            := (rem_is_identity_when_mltn hyzero h_pos hylt).symm
           rw [hyrem]
           change rem y n hyzero h_pos = d.r
           rw [← rem_is_identity_when_mltn d.rnat h_pos d.lt,
               ← cong_mod_iff_rem_eq hyzero d.rnat h_pos]
           exact hcong


----------------------------- Lecture 07 -----------------------------

-- Proposition 63
theorem modulo_reciprocal {m k : ℤ}
   (h_pos : m > 0) :
   (∃ l, 0 ≤ l ∧ l < m ∧ k * l ≡ 1 [ZMOD m])
   ↔ (∃ i j : ℤ, i * k + j * m = 1)
:= by constructor
      · intro he
        obtain ⟨ l, ⟨ _, _ , hl ⟩ ⟩ := he
        have hdiv : ∃ a : ℤ, (k * l) - 1 = a * m
          := by apply Int.ModEq.dvd at hl
                obtain ⟨ b , hb ⟩ := hl
                exists -b
                linarith [hb]
        obtain ⟨ a, ha ⟩ := hdiv
        exists l, -a
        linarith [ha]
      · intro he
        obtain ⟨ i, j, hlin ⟩ := he
        have hdiv : m ∣ 1 - k * i
            := by exists j
                  linarith
        have hmod : k * i ≡ 1 [ZMOD m]
            := Int.modEq_iff_dvd.mpr hdiv
        have hnorm : ∃! inorm, i ≡ inorm [ZMOD m]
                             ∧ 0 ≤ inorm ∧ inorm < m
            := modulo_arithmetic_int h_pos
        obtain ⟨inorm, ⟨⟨inormcong, ⟨inormlb, inormub⟩⟩, _⟩⟩ := hnorm
        exists inorm
        have hmod' : k * i ≡ k * inorm [ZMOD m]
            := Int.ModEq.mul_left k inormcong
        have hmod'' : k * inorm ≡ 1 [ZMOD m]
            := hmod'.symm.trans hmod
        constructor
        · exact inormlb
        · constructor
          · exact inormub
          · exact hmod''

-- Definition 64
def linear_combination (r m n : ℤ) : Prop
   := ∃ s t : ℤ, s * m + t * n = r

lemma dvd_linear_comb {a b d x y : ℤ}
    (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ x * a + y * b := by
  have h1 : d ∣ x * a := dvd_mul_of_dvd_right ha x
  have h2 : d ∣ y * b := dvd_mul_of_dvd_right hb y
  exact dvd_add h1 h2

-- Proposition 65
theorem modulo_reciprocal' {m k : ℤ}
   (h_pos : m > 0) :
   (∃ l, 0 ≤ l ∧ l < m ∧ k * l ≡ 1 [ZMOD m])
   ↔ linear_combination 1 k m
:= by dsimp [linear_combination]
      exact modulo_reciprocal h_pos

def D (m : ℤ) (_hm : 0 ≤ m) : Set ℤ
  := { d : ℤ | 0 ≤ d ∧  d ∣ m }

def CD (m : ℤ) (n : ℤ) (_hm : 0 ≤ m) (_hn : 0 ≤ n) : Set ℤ
  := { d : ℤ | 0 ≤ d ∧ d ∣ m ∧ d ∣ n }

-- Lemma 71
lemma common_divisor_mod {m m' n : ℤ}
    (hm : 0 ≤ m) (hm' : 0 ≤ m') (hn : 0 ≤ n) :
    m ≡ m' [ZMOD n] → CD m n hm hn = CD m' n hm' hn
  := by intro hmod_cong
        dsimp [CD]
        ext d
        constructor
        · intro h
          rcases h with ⟨h_d_nonneg, h_d_div_m, h_d_div_n⟩
          have hmod_cong_d : m ≡ m' [ZMOD d]
            := Int.ModEq.of_dvd h_d_div_n hmod_cong
          have h_d_div_m' : d ∣ m'
            := by rw [Int.ModEq.dvd_iff hmod_cong_d] at h_d_div_m
                  exact h_d_div_m
          exact ⟨h_d_nonneg, h_d_div_m', h_d_div_n⟩
        · intro h
          rcases h with ⟨h_d_nonneg, h_d_div_m', h_d_div_n⟩
          have hmod_cong_d : m ≡ m' [ZMOD d]
            := Int.ModEq.of_dvd h_d_div_n hmod_cong
          have h_d_div_m : d ∣ m
            := by rw [← Int.ModEq.dvd_iff hmod_cong_d] at h_d_div_m'
                  exact h_d_div_m'
          exact ⟨h_d_nonneg, h_d_div_m, h_d_div_n⟩

lemma common_divisor_symm {m n : ℤ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) :
    CD m n hm hn = CD n m hn hm
  := by dsimp [CD]
        ext d
        constructor
        · intro h
          rcases h with ⟨h_d_nonneg, h_d_div_m, h_d_div_n⟩
          exact ⟨h_d_nonneg, h_d_div_n, h_d_div_m⟩
        · intro h
          rcases h with ⟨h_d_nonneg, h_d_div_n, h_d_div_m⟩
          exact ⟨h_d_nonneg, h_d_div_m, h_d_div_n⟩

----------------------------- Lecture 08 -----------------------------

-- Lemma 73
lemma common_divisor_rem_1 {m n : ℤ}
    (hm : 0 < m) (hn : 0 < n) :
    (hdiv : n ∣ m)
    → (CD m n (Int.le_of_lt hm) (Int.le_of_lt hn))
      = D n (Int.le_of_lt hn)
  := by intro hdiv
        dsimp [CD, D]
        ext d
        constructor
        · intro h
          rcases h with ⟨ h_d_nonneg, _, h_d_div_n ⟩
          exact ⟨ h_d_nonneg, h_d_div_n ⟩
        · intro h
          rcases h with ⟨ h_d_nonneg, h_d_div_n ⟩
          have h_d_div_m : d ∣ m
            := h_d_div_n.trans hdiv
          exact ⟨ h_d_nonneg, h_d_div_m, h_d_div_n ⟩

theorem common_divisor_rem_2 {m n : ℤ}
    (hm : 0 < m) (hn : 0 < n) :
    (hndiv : ¬ (n ∣ m))
    → (CD m n (Int.le_of_lt hm) (Int.le_of_lt hn))
      = (CD n (rem m n (Int.le_of_lt hm) hn)
              (Int.le_of_lt hn) (rem_nonneg m n (Int.le_of_lt hm) hn))
  := by intro hndiv
        let r := rem m n (Int.le_of_lt hm) hn
        let hr := rem_nonneg m n (Int.le_of_lt hm) hn
        have h_cd_symm :
            (CD m n (Int.le_of_lt hm) (Int.le_of_lt hn))
            = (CD n m (Int.le_of_lt hn) (Int.le_of_lt hm))
          := common_divisor_symm (Int.le_of_lt hm) (Int.le_of_lt hn)
        have hcong : m ≡ r [ZMOD n]
          := modulo_arithmetic_nat (Int.le_of_lt hm) hn
        have heq1 :
            (CD m n (Int.le_of_lt hm) (Int.le_of_lt hn))
            = (CD r n hr (Int.le_of_lt hn))
          := common_divisor_mod (Int.le_of_lt hm) hr (Int.le_of_lt hn) hcong
        have heq2 :
            (CD r n hr (Int.le_of_lt hn))
            = (CD n r (Int.le_of_lt hn) hr)
          := common_divisor_symm hr (Int.le_of_lt hn)
        have heq3 :
            (CD m n (Int.le_of_lt hm) (Int.le_of_lt hn))
             = (CD n r (Int.le_of_lt hn) hr)
          := heq1.trans heq2
        exact heq3

def is_gcd (k m n : ℤ) (_hm : 0 ≤ m) (_hn : 0 ≤ n) (_hk : 0 ≤ k) : Prop
  := k ∣ m ∧ k ∣ n ∧
     ∀ (d : ℤ), 0 ≤ d → d ∣ m ∧ d ∣ n → d ∣ k

-- Euclid's Algorithm
structure GCDState (m n : ℤ) where
  d : ℤ
  hm : d ∣ m
  hn : d ∣ n
  greatest : ∀ d', d' ∣ m ∧ d' ∣ n → d' ∣ d

def euclid_algo : (m n : ℤ) → (hm : m ≥ 0) → (hn : n > 0) → GCDState m n
  := fun m => fun n => fun hm => fun hn =>
      let ⟨ q, r, heq, hlt, hqnat, hrnat ⟩
        := division_algorithm m n hm hn;
      if h : 0 = r then
        have hn : n ∣ n := by trivial
        have hm : n ∣ m := by rw [← h] at heq
                              exists q
                              linarith
        have hg : ∀ d', d' ∣ m ∧ d' ∣ n → d' ∣ n
          := by intro d' ⟨ hdivm, hdivn ⟩
                exact hdivn
        ⟨n, hm, hn, hg⟩
      else
        have hr : r > 0 := lt_of_le_of_ne hrnat h
        let ⟨d, hdn, hdr, hg⟩ := euclid_algo n r (Int.le_of_lt hn) hr;
        have hdm : d ∣ m := by rw [heq, ← one_mul r]
                               apply dvd_linear_comb hdn hdr
        have hg : ∀ d', d' ∣ m ∧ d' ∣ n → d' ∣ d
          := by intro d' ⟨ hdivm, hdivn ⟩
                have hdivr : d' ∣ r
                  := by have heq': 1 * m + (-q) * n = r := by linarith
                        rw [← heq']
                        apply dvd_linear_comb hdivm hdivn
                specialize hg d'
                apply hg ⟨hdivn, hdivr⟩
        ⟨d, hdm, hdn, hg⟩
    termination_by m n _ _ => n.toNat
    decreasing_by
      simp_wf
      exact ⟨hlt, hn⟩

-- Example 74
#eval (euclid_algo 34 13 (by norm_num) (by norm_num)).d

-- Proposition 75
theorem uniqueness_of_gcd {m n a b : ℤ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    CD m n hm hn = D a ha → CD m n hm hn = D b hb
    → a = b
  := by
    dsimp [CD, D]
    intro cd_eq_da cd_eq_db
    have div_cd_iff_div_a : ∀ d : ℤ, 0 ≤ d → (d ∣ m ∧ d ∣ n ↔ d ∣ a)
      := by intro d hd0
            rw [Set.ext_iff] at cd_eq_da
            simp only [Set.mem_setOf_eq, and_congr_right_iff] at cd_eq_da
            apply cd_eq_da d hd0
    have div_cd_iff_div_b : ∀ d : ℤ, 0 ≤ d → (d ∣ m ∧ d ∣ n ↔ d ∣ b)
      := by intro d hd0
            rw [Set.ext_iff] at cd_eq_db
            simp only [Set.mem_setOf_eq, and_congr_right_iff] at cd_eq_db
            apply cd_eq_db d hd0
    have div_a_iff_div_b : ∀ d : ℤ, 0 ≤ d → (d ∣ a ↔ d ∣ b) := by
      intro d hd0
      exact ((div_cd_iff_div_a d hd0).symm).trans (div_cd_iff_div_b d hd0)
    have a_dvd_b : a ∣ b := (div_a_iff_div_b a ha).mp (dvd_refl a)
    have b_dvd_a : b ∣ a := (div_a_iff_div_b b hb).mpr (dvd_refl b)
    exact Int.dvd_antisymm ha hb a_dvd_b b_dvd_a

-- Proposition 76
theorem defs_of_gcd_equiv {m n k : ℤ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) (hk : 0 ≤ k) :
     (k ∣ m ∧ k ∣ n ∧ ∀ (d : ℤ), 0 ≤ d → d ∣ m ∧ d ∣ n → d ∣ k)
     ↔ CD m n hm hn = D k hk
  := by dsimp [CD, D]
        constructor
        · intro ⟨hkdivm, hkdivn, hkgreatest⟩
          ext d
          simp only [Set.mem_setOf_eq, and_congr_right_iff]
          intro hd0
          specialize hkgreatest d
          constructor
          · exact hkgreatest hd0
          · intro hddivk
            exact ⟨hddivk.trans hkdivm, hddivk.trans hkdivn⟩
        · intro hdef2
          rw [Set.ext_iff] at hdef2
          constructor
          · specialize hdef2 k
            simp only [Set.mem_setOf_eq, hk, true_and] at hdef2
            have hrefl : k ∣ k := by trivial
            have ⟨hdivm, hdivn⟩ : k ∣ m ∧ k ∣ n := by rw [hdef2]
            exact hdivm
          · constructor
            · specialize hdef2 k
              simp only [Set.mem_setOf_eq, hk, true_and] at hdef2
              have hrefl : k ∣ k := by trivial
              have ⟨hdivm, hdivn⟩ : k ∣ m ∧ k ∣ n := by rw [hdef2]
              exact hdivn
            · intro d hd
              specialize hdef2 d
              simp only [Set.mem_setOf_eq, hd, true_and] at hdef2
              exact hdef2.mp

def gcd : (m n : ℤ) → (hm : m ≥ 0) → (hn : n > 0) → ℤ
  := fun m => fun n => fun hm => fun hn =>
      (euclid_algo m n hm hn).d
