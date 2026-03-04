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

@[simp]
def quo : (m : ℤ) → (n : ℤ) → (m ≥ 0) → (n > 0) → ℤ :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).q

@[simp]
def quo_nonneg : (m : ℤ) → (n : ℤ) → (hm : m ≥ 0) → (hn : n > 0) →
                  0 ≤ (quo m n hm hn) :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).qnat

@[simp]
def rem : (m : ℤ) → (n : ℤ) → (m ≥ 0) → (n > 0) → ℤ :=
  fun m => fun n => fun pm => fun pn =>
    (division_algorithm m n pm pn).r

@[simp]
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

theorem division_algorithm_result_unique {m n a b : ℤ}
   (hm : 0 ≤ m) (hn : 0 < n) (ha : 0 ≤ a) (hbl : 0 ≤ b) (hbu : b < n)
   (heq : m = a * n + b) :
    a = quo m n hm hn ∧ b = rem m n hm hn
 := by let res := division_algorithm m n hm hn
       let eq := res.eq
       have ⟨⟨q, r⟩, ⟨_, _, _, eq⟩, unique⟩ := division_theorem hm hn;
       have habqr : (a, b) = (q, r)
        := unique (a, b) ⟨ha, hbl, hbu, heq⟩;
       have hquoremqr : (res.q, res.r) = (q, r)
        := unique (res.q, res.r) ⟨res.qnat, res.rnat, res.lt, res.eq⟩;
       have ⟨h_a_eq_q, h_b_eq_r⟩ := Prod.mk.inj habqr
       have ⟨h_quo_eq_q, h_rem_eq_r⟩ := Prod.mk.inj hquoremqr
       exact ⟨h_a_eq_q.trans h_quo_eq_q.symm,
              h_b_eq_r.trans h_rem_eq_r.symm ⟩

theorem rem_eq_zero_iff_dvd {m n : ℤ} (hm : 0 ≤ m) (hn : 0 < n) :
    rem m n hm hn = 0 ↔ n ∣ m
 := by let res := division_algorithm m n hm hn
       let eq := res.eq
       let q := res.q
       let r := res.r
       constructor
       · intro heq
         dsimp [rem] at heq
         rw [heq, add_zero, mul_comm] at eq
         exact ⟨q, eq⟩
       · intro h_n_div_m
         obtain ⟨ a, ha ⟩ := h_n_div_m
         have h_eq : m = a * n + 0
            := by rw [mul_comm, ← add_zero (a*n)] at ha
                  exact ha
         have hal : 0 ≤ a
          := by rw [h_eq, add_zero] at hm
                rw [mul_nonneg_iff_left_nonneg_of_pos hn] at hm
                exact hm
         have ⟨hquo, hrem⟩ : a = q ∧ 0 = r
          := division_algorithm_result_unique hm hn hal (Int.le_refl 0) hn h_eq
         exact hrem.symm

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
             · linarith [d.lt]
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

lemma common_divisor_refl {m n : ℤ}
    (hm : 0 ≤ m) (hn : 0 ≤ n) :
    CD m n hm hn = CD m n hm hn
  := by dsimp [CD]

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

-- Euclid's Algorithm (simple)
def euclid_algo_simp : (m n : ℤ) → (hm : m ≥ 0) → (hn : n > 0) → ℤ
  := fun m => fun n => fun hm => fun hn =>
      let ⟨ _q, r, _heq, hlt, _hqnat, hrnat ⟩
        := division_algorithm m n hm hn;
      if h : 0 = r then
        n
      else
        have hr : r > 0 := lt_of_le_of_ne hrnat h
        let d := euclid_algo_simp n r (Int.le_of_lt hn) hr;
        d
    termination_by m n _ _ => n.toNat
    decreasing_by
      simp_wf
      exact ⟨hlt, hn⟩

-- Example 74
#eval euclid_algo_simp 34 13 (by norm_num) (by norm_num)

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
          have hdef2k := hdef2 k
          simp only [Set.mem_setOf_eq, hk, true_and] at hdef2k
          have hrefl : k ∣ k := by trivial
          have ⟨hdivm, hdivn⟩ : k ∣ m ∧ k ∣ n := by rw [hdef2k]
          constructor
          ·exact hdivm
          · constructor
            · exact hdivn
            · intro d hd
              specialize hdef2 d
              simp only [Set.mem_setOf_eq, hd, true_and] at hdef2
              exact hdef2.mp

-- Definition 77
def is_gcd (k m n : ℤ) (_hk : k > 0) (_hm : m > 0) (_hn : n > 0) : Prop
  := k ∣ m ∧ k ∣ n ∧ ∀ (d : ℤ), 0 ≤ d → d ∣ m ∧ d ∣ n → d ∣ k

structure GCDState (m n : ℤ) (hm : 0 < m) (hn : 0 < n) where
  d : ℤ
  hd : 0 < d
  hgcd : CD m n (Int.le_of_lt hm) (Int.le_of_lt hn) = D d (Int.le_of_lt hd)

def euclid_algo : (m n : ℤ) → (hm : m > 0) → (hn : n > 0)
                  → GCDState m n hm hn
  := fun m => fun n => fun hm => fun hn =>
      let res := division_algorithm m n (Int.le_of_lt hm) hn;
      let q := res.q
      let r := res.r
      have heq := res.eq
      have hlt := res.lt
      have hrnat := res.rnat
      have hrfl : r = res.r
        := by rfl
      if h : r = 0 then
         have hndvdm : n ∣ m
            := by rw [← hrfl, h, add_zero, mul_comm] at heq
                  exists q
        ⟨n, hn, common_divisor_rem_1 hm hn hndvdm⟩
      else
        have hr : 0 < r := lt_of_le_of_ne hrnat (fun hr0 => h hr0.symm)
        let ⟨d, hd, hgcd⟩ := euclid_algo n r hn hr;
        have h_n_not_div_m : ¬ (n ∣ m)
          := (rem_eq_zero_iff_dvd (Int.le_of_lt hm) hn).not.mp h
        have hlem :
          CD m n (Int.le_of_lt hm) (Int.le_of_lt hn) = CD n res.r (Int.le_of_lt hn) hrnat
          := common_divisor_rem_2 hm hn h_n_not_div_m
        ⟨d, hd, hlem.trans hgcd⟩
    termination_by m n _ _ => n.toNat
    decreasing_by
      simp_wf
      exact ⟨hlt, hn⟩

@[simp] def gcd_comp (m n : ℤ) (hm : m > 0) (hn : n > 0) : ℤ
  := (euclid_algo m n hm hn).d


@[simp] def gcd_comp_is_pos (m n : ℤ) (hm : m > 0) (hn : n > 0) :
    0 < (gcd_comp m n hm hn)
  := (euclid_algo m n hm hn).hd

-- Theorem 78
theorem euclid_algo_computes_gcd (m n : ℤ) (hm : m > 0) (hn : n > 0) :
    is_gcd (gcd_comp m n hm hn) m n (gcd_comp_is_pos m n hm hn) hm hn
  := by dsimp [is_gcd]
        let ⟨ d, hd, hgcd ⟩ := euclid_algo m n hm hn
        rw [defs_of_gcd_equiv (Int.le_of_lt hm) (Int.le_of_lt hn) (Int.le_of_lt hd)]
        exact hgcd

lemma dvd_gcd_comp {d m n : ℤ} (hd : d > 0) (hm : m > 0) (hn : n > 0) :
    d ∣ (gcd_comp m n hm hn) ↔ d ∣ m ∧ d ∣ n
  := by dsimp [gcd_comp]
        let e := euclid_algo m n hm hn
        let gd := e.d
        let hgd := e.hgcd
        constructor
        · intro hdvd
          dsimp [CD, D] at hgd
          rw [Set.ext_iff] at hgd
          simp only [Set.mem_setOf_eq, and_congr_right_iff] at hgd
          specialize hgd d
          have h_iff : d ∣ m ∧ d ∣ n ↔ d ∣ gd := hgd (Int.le_of_lt hd)
          rw [h_iff]
          exact hdvd
        · intro ⟨ hdvdm, hdvdn ⟩
          let hup : ∀ (d : ℤ), 0 ≤ d → d ∣ m ∧ d ∣ n → d ∣ gd
              := by rw [← defs_of_gcd_equiv (Int.le_of_lt hm) (Int.le_of_lt hn)] at hgd
                    exact hgd.2.2
          specialize hup d
          have h_exact : d ∣ gd
            := hup (Int.le_of_lt hd) ⟨ hdvdm, hdvdn ⟩
          exact h_exact

-- Lemma 80
lemma gcd_commutative (m n : ℤ) (hm : 0 < m) (hn : 0 < n) :
    gcd_comp m n hm hn = gcd_comp n m hn hm
:= by dsimp [gcd_comp]
      let ⟨d1, h_d1, h_eq1⟩ := euclid_algo m n hm hn
      let ⟨d2, h_d2, h_eq2⟩ := euclid_algo n m hn hm
      simp only
      suffices h :
        CD m n (Int.le_of_lt hm) (Int.le_of_lt hn)
        = CD n m (Int.le_of_lt hn) (Int.le_of_lt hm)
        by have h' : CD m n (Int.le_of_lt hm) (Int.le_of_lt hn)
                     = D d2 (Int.le_of_lt h_d2)
                    := by rw [← h] at h_eq2; exact h_eq2
           apply uniqueness_of_gcd (Int.le_of_lt hm) (Int.le_of_lt hn)
            (Int.le_of_lt h_d1) (Int.le_of_lt h_d2) h_eq1 h'
      exact common_divisor_symm (Int.le_of_lt hm) (Int.le_of_lt hn)

theorem gcd_associative (l m n : ℤ)
    (hl : l > 0) (hm : m > 0) (hn : n > 0) :
    gcd_comp l (gcd_comp m n hm hn) hl (gcd_comp_is_pos m n hm hn)
    = gcd_comp (gcd_comp l m hl hm)  n (gcd_comp_is_pos l m hl hm) hn
  := by
        simp only [gcd_comp]
        -- gcd(m, n)
        let e_mn := euclid_algo m n hm hn
        let d_mn := e_mn.d
        let hd_mn := e_mn.hd
        let hgcd_dmn := euclid_algo_computes_gcd m n hm hn
        dsimp [is_gcd] at hgcd_dmn
        let ⟨dmn_dvd_m, dmn_dvd_dn, gcdup_dmn⟩ := hgcd_dmn
        -- gcd(l, m)
        let e_lm := euclid_algo l m hl hm
        let d_lm := e_lm.d
        let hd_lm := e_lm.hd
        let hgcd_dlm := euclid_algo_computes_gcd l m hl hm
        dsimp [is_gcd] at hgcd_dlm
        let ⟨dlm_dvd_l, dlm_dvd_dm, gcdup_dlm⟩ := hgcd_dlm
        -- gcd (l, gcd(m, n))
        let e1 := euclid_algo l d_mn hl hd_mn
        let d1 := e1.d
        let h_d1 := e1.hd
        let hgcd_d1 := euclid_algo_computes_gcd l d_mn hl hd_mn
        dsimp [is_gcd] at hgcd_d1
        let ⟨d1_dvd_l, d1_dvd_dmn, gcdup_d1⟩ := hgcd_d1
        -- gcd (gcd(l, m), n)
        let e2 := euclid_algo d_lm n hd_lm hn
        let d2 := e2.d
        let h_d2 := e2.hd
        let hgcd_d2 := euclid_algo_computes_gcd d_lm n hd_lm hn
        let ⟨d2_dvd_dlm, d2_dvd_n, gcdup_d2⟩ := hgcd_d2
        have h_d1_dvd_d2 : d1 ∣ d2
          := by have ⟨ d1_dvd_m, d1_dvd_n ⟩
                  := (dvd_gcd_comp h_d1 hm hn).mp d1_dvd_dmn
                specialize gcdup_dlm d1
                have d1_dvd_dlm : d1 ∣ d_lm
                  := gcdup_dlm (Int.le_of_lt h_d1) ⟨ d1_dvd_l, d1_dvd_m ⟩
                specialize gcdup_d2 d1
                exact gcdup_d2 (Int.le_of_lt h_d1) ⟨ d1_dvd_dlm, d1_dvd_n ⟩
        have h_d2_dvd_d1 : d2 ∣ d1
          := by have ⟨ d2_dvd_l, d2_dvd_m ⟩
                  := (dvd_gcd_comp h_d2 hl hm).mp d2_dvd_dlm
                specialize gcdup_dmn d2
                have d2_dvd_dmn : d2 ∣ d_mn
                  := gcdup_dmn (Int.le_of_lt h_d2) ⟨ d2_dvd_m, d2_dvd_n ⟩
                specialize gcdup_d1 d2
                exact gcdup_d1 (Int.le_of_lt h_d2) ⟨ d2_dvd_l, d2_dvd_dmn ⟩
        exact Int.dvd_antisymm (Int.le_of_lt h_d1) (Int.le_of_lt h_d2) h_d1_dvd_d2 h_d2_dvd_d1

structure ExtendedGCDState (m n : ℤ) (hm : 0 < m) (hn : 0 < n) where
  s : ℤ
  t : ℤ
  r : ℤ
  hr : r > 0
  hlin : r = s * m + t * n
  hgcd : CD m n (Int.le_of_lt hm) (Int.le_of_lt hn) = D r (Int.le_of_lt hr)

def gcd_iter (m n : ℤ) (hm : m > 0) (hn : n > 0) :
    (s1 t1 r1 s2 t2 r2: ℤ)
  → (hr1 : r1 > 0) → (hr2 : r2 > 0)
  → (hlin1 : r1 = s1 * m + t1 * n)
  → (hlin2 : r2 = s2 * m + t2 * n)
  → (hcd : CD m n (Int.le_of_lt hm) (Int.le_of_lt hn)
          = CD r1 r2 (Int.le_of_lt hr1) (Int.le_of_lt hr2))
  → ExtendedGCDState m n hm hn
 := fun s1 => fun t1 => fun r1 => fun s2 => fun t2 => fun r2 => fun hr1 => fun hr2 =>
    fun hlin1 => fun hlin2 => fun hcd =>
      let res := division_algorithm r1 r2 (Int.le_of_lt hr1) hr2;
      let q := res.q
      let r := res.r
      have heq := res.eq
      have hlt := res.lt
      have hrnat := res.rnat
      have hrfl : r = res.r
        := by rfl
      if h : r = 0 then
         have hr2dvdr1 : r2 ∣ r1
            := by rw [← hrfl, h, add_zero, mul_comm] at heq
                  exists q
         have hd : CD r1 r2 (Int.le_of_lt hr1) (Int.le_of_lt hr2) = D r2 (Int.le_of_lt hr2)
            := common_divisor_rem_1 hr1 hr2 hr2dvdr1
        ⟨s2, t2, r2, hr2, hlin2, hcd.trans hd⟩
      else
        have hr : 0 < r := lt_of_le_of_ne hrnat (fun hr0 => h hr0.symm)
        have h_r2_not_div_r1 : ¬ (r2 ∣ r1)
          := (rem_eq_zero_iff_dvd (Int.le_of_lt hr1) hr2).not.mp h
        have hrlc : r = (s1-q*s2) * m + (t1-q*t2) * n
          := by calc
              r = r1 - q * r2 := by linarith [heq]
              _ = (s1 * m + t1 * n) - q * (s2 * m + t2 * n) := by rw [hlin1, hlin2]
              _ =  (s1 - (q * s2)) * m + (t1 - (q * t2)) * n := by linarith
        have hcd' : CD m n (Int.le_of_lt hm) (Int.le_of_lt hn)
                 = CD r2 r (Int.le_of_lt hr2) (Int.le_of_lt hr)
          := hcd.trans (common_divisor_rem_2 hr1 hr2 h_r2_not_div_r1)
        gcd_iter m n hm hn s2 t2 r2 (s1-q*s2) (t1-q*t2) r hr2 hr hlin2 hrlc hcd'
     termination_by _ _ _ _ _ r2 => r2.toNat
     decreasing_by
      simp_wf
      exact ⟨hlt, hr2⟩

def extended_euclid_algorithm : (m n : ℤ) → (hm : m > 0) → (hn : n > 0)
                              → ExtendedGCDState m n hm hn
    := fun m => fun n => fun hm => fun hn =>
    have h1 : m = 1 * m + 0 * n := by linarith
    have h2 : n = 0 * m + 1 * n := by linarith
    have hcd := common_divisor_refl (Int.le_of_lt hm) (Int.le_of_lt hn)
    gcd_iter m n hm hn 1 0 m 0 1 n hm hn h1 h2 hcd
