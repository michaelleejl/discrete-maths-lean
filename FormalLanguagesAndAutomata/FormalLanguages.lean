import Mathlib.Data.Set.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Group.Defs

namespace FormalLanguagesAndAutomata

-- Section 1, "Formal languages"

-- Definition 1.1, "Alphabet"
def Alphabet {t} (symbols : Finset t) : Type :=
  { x : t // x ∈ symbols }

-- For example, this is an alphabet of characters, which has three symbols: 'a', 'b', and 'c'.
example : Type := Alphabet {'a', 'b', 'c'}

-- Definition 1.2, "String over an alphabet"
def Strings {t} (symbols : Finset t) := List (Alphabet symbols)

example : Strings {'a', 'b', 'c'} :=
  [⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩]

def String {t} (symbols : Finset t) n :=
  { s : Strings symbols // s.length = n }

example : String {'a', 'b', 'c'} 3 :=
  ⟨[⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩], rfl⟩

-- Definition 1.3, "Concatenation of strings"
namespace Strings

@[simp]
def concat {t} {symbols : Finset t}
  (s₁ : Strings symbols) (s₂ : Strings symbols)
  : Strings symbols :=
  List.append s₁ s₂

instance : Append (Strings α) where
  append := concat

@[simp]
theorem concat_eq {t} {symbols : Finset t} (s₁ s₂ : Strings symbols) :
  s₁ ++ s₂ = List.append s₁ s₂ := rfl

-- Lemma 1.4, "Properties of concatenation"

@[simp]
def empty {t} {symbols : Finset t} : Strings symbols :=
  []

notation "ε" => empty

lemma eps_concat {t} {symbols : Finset t}
  : ∀ (s : Strings symbols), ε ++ s = s := by simp

lemma concat_eps {t} {symbols : Finset t}
  : ∀ (s : Strings symbols), s ++ ε = s := by simp

lemma concat_assoc {t} {symbols : Finset t}
  : ∀ (s₁ s₂ s₃ : Strings symbols),
  (s₁ ++ s₂) ++ s₃
  = s₁ ++ (s₂ ++ s₃) := by simp

-- Observation 1.5, "Monoid structure of strings"
instance {symbols : Finset t} : Monoid (Strings symbols) where
  one := ε
  mul := concat
  one_mul := eps_concat
  mul_one := concat_eps
  mul_assoc := concat_assoc

end Strings

-- Definition 1.6, "Formal language"
def FormalLanguage {t} (symbols : Finset t) :=
  Set (Strings symbols)

-- Section 2, "Inductive definitions"

-- Example 2.1.1, "Informal rules for constructing naturals"
namespace Examples.E2_1_1
inductive ExampleNat : Type
  | zero : ExampleNat
  | succ (n : ExampleNat) : ExampleNat
end Examples.E2_1_1

-- Definition 2.1.4.1, "Syntactic rule"
-- Note, for theorems about syntactic rules, we will use this definition,
--   otherwise we will just use Lean's `inductive` for the formalizations
structure SyntacticRule (X : Set t) where
  premises : List X
  conclusion : X

@[simp]
def set_of_type (X : Type) : Set X := Set.univ

namespace SyntacticRule

@[simp]
def premise_values {X : Set t} (r : SyntacticRule X) : List t :=
  List.map (fun x => x.val) r.premises

lemma in_premise_only_if_in_premise_values {X : Set t} (r : SyntacticRule X)
  : ∀ u (h_umem : u ∈ X), ⟨u, h_umem⟩ ∈ r.premises → u ∈ r.premise_values := by
  intro u h_umem h_in_premises
  suffices ∃ (h : u ∈ X), ⟨u, h⟩ ∈ r.premises by
    simp [this]
  use h_umem

@[simp]
lemma premise_values_eq_nil_only_if_premises_eq_nil {X : Set t} (r : SyntacticRule X)
  : r.premise_values = [] → r.premises = [] := by
  intro h
  dsimp [premise_values] at h
  apply List.map_eq_nil_iff.mp at h
  exact h

lemma premise_values_eq_nil_if_premises_eq_nil {X : Set t} (r : SyntacticRule X)
  : r.premises = [] → r.premise_values = [] := by
  intro h
  dsimp [premise_values]
  apply List.map_eq_nil_iff.mpr
  exact h

theorem premise_values_eq_nil_iff_premises_eq_nil {X : Set t} (r : SyntacticRule X)
  : r.premise_values = [] ↔ r.premises = [] := by
  constructor
  · exact premise_values_eq_nil_only_if_premises_eq_nil r
  · exact premise_values_eq_nil_if_premises_eq_nil r

@[simp]
def conclusion_value {X : Set t} (r : SyntacticRule X) : t :=
  r.conclusion.1

@[simp]
def is_axiom (r : SyntacticRule t) : Prop :=
  List.isEmpty r.premises

lemma is_axiom_only_if_premises_eq_nil
  (r : SyntacticRule t)
  : r.is_axiom → r.premises = [] := by simp

lemma is_axiom_only_if_premise_values_eq_nil
  (r : SyntacticRule t)
  : r.is_axiom → r.premise_values = [] := by
  intro h_axiom
  suffices r.premises = [] by
    exact premise_values_eq_nil_if_premises_eq_nil r
      (is_axiom_only_if_premises_eq_nil r h_axiom)
  exact is_axiom_only_if_premises_eq_nil r h_axiom

-- Example 2.1.4.2, "Syntactic rules for forming natural numbers"
namespace Examples.E2_1_4_2

@[simp]
def ℝ' := set_of_type ℝ

@[simp]
def zero : SyntacticRule ℝ' :=
  { premises := [], conclusion := ⟨0, by simp⟩ }

@[simp]
def succ (x : ℝ) : SyntacticRule ℝ' :=
  { premises := [⟨x, by simp⟩], conclusion := ⟨x + 1, by simp⟩ }

@[simp]
def nat_rules : Set (SyntacticRule ℝ') :=
  Set.union
    { zero }
    { succ n | n : ℕ }

end Examples.E2_1_4_2

-- Definition 2.1.4.3, "The closure condition denoted by a syntactic rule"
def closure_condition {X : Set t} (r : SyntacticRule X) : Set (Set t) :=
  {
    S ⊆ X
    | (∀ u ∈ r.premise_values, u ∈ S) → (r.conclusion_value ∈ S)
  }

def closure_conditions_inter {X : Set t} (R : Set (SyntacticRule X))
  : Set (Set t) :=
  Set.sInter { closure_condition r | r ∈ R }

def Cl {X : Set t} (R : Set (SyntacticRule X)) :=
  closure_conditions_inter R

def in_Cl_if_closed {X : Set t}
  (R : Set (SyntacticRule X)) (S : Set t)
  : S ⊆ X
    → (∀ r ∈ R, (∀ u ∈ r.premise_values, u ∈ S) → r.conclusion_value ∈ S)
    → S ∈ Cl R := by
  intro h_subset h_closed
  dsimp [Cl, closure_conditions_inter]
  intro Y hY
  rcases hY with ⟨r, h_rmem, hY_eq⟩
  rw [← hY_eq]
  dsimp [closure_condition]
  exact ⟨h_subset, h_closed r h_rmem⟩

-- Definition 2.1.5
inductive Derivation {X : Set t} (R : Set (SyntacticRule X))
  : t → Type where
  | ax
    : r ∈ R
    → is_axiom r
    → Derivation R r.conclusion_value
  | with_premises
    : r ∈ R
    → (∀ u, u ∈ r.premise_values → Derivation R u)
    → Derivation R r.conclusion_value

namespace Derivation

@[simp]
def derives {X : Set t} (R : Set (SyntacticRule X)) (x : t) : Prop :=
  Nonempty (Derivation R x)

-- Note that this is defined with axioms having a height of 0, for convenience
@[simp]
def height {X : Set t} {R : Set (SyntacticRule X)} : Derivation R x → ℕ
  | ax _ _ => 0
  | @with_premises _ _ _ r _ h_premises =>
    Option.getD
      (List.max?
        (List.map
          (fun ⟨u, h_umem⟩ => height (h_premises u h_umem))
          (List.attach r.premise_values)))
      0

example
  : Derivation
    Examples.E2_1_4_2.nat_rules
    1
  := by
  suffices h_premise : Derivation Examples.E2_1_4_2.nat_rules 0 by
    -- Assuming a derivation of 0, we form a derivation of 1
    let r := Examples.E2_1_4_2.succ 0
    let h_rmem : r ∈ Examples.E2_1_4_2.nat_rules := by
      dsimp
      right
      use 0
      simp [r]
    let h_premises : ∀ u, u ∈ r.premise_values → Derivation Examples.E2_1_4_2.nat_rules u := by
       intro u u_mem
       apply List.mem_singleton.mp at u_mem
       rw [u_mem]
       exact h_premise
    let r_conc_1 : 1 = r.conclusion_value := by
      simp [r]
    rw [r_conc_1]
    apply (Derivation.with_premises h_rmem h_premises)
  let r := Examples.E2_1_4_2.zero
  let h_rmem : r ∈ Examples.E2_1_4_2.nat_rules := by
    dsimp
    left
    rfl
  let h_premises_empty : is_axiom r := by simp [r]
  apply (Derivation.ax h_rmem h_premises_empty)

end Derivation

end SyntacticRule

-- Definition 2.1.7, "Syntactic presentation of a formal language"
def FormalLanguageSyntacticPresentation
  (symbols : Finset t) :=
  Set (SyntacticRule (set_of_type (Strings symbols)))

-- Example 2.1.8, "A syntactic presentation of a formal language"
namespace Examples.E2_1_8
def ExampleLanguage : FormalLanguageSyntacticPresentation {'a', 'b'} :=
  Set.sUnion {
    (Set.singleton {premises := [], conclusion := ⟨ε, by simp⟩}),
    { {
        premises := [⟨u, by simp⟩],
        conclusion := ⟨Strings.concat
          [⟨'a', by simp⟩]
          (Strings.concat u [⟨'b', by simp⟩]), by simp⟩}
      | u },
    { {
        premises := [⟨u, by simp⟩],
        conclusion := ⟨Strings.concat
          [⟨'b', by simp⟩]
          (Strings.concat u [⟨'a', by simp⟩]), by simp⟩}
      | u },
    { {
        premises := [⟨u, by simp⟩, ⟨v, by simp⟩],
        conclusion := ⟨Strings.concat u v, by simp⟩}
      | (u : Strings {'a', 'b'})
        (v : Strings {'a', 'b'}) }
  }
end Examples.E2_1_8

-- Example 2.1.9, "Revisiting reflexive-transitive closure"
namespace Examples.E2_1_9
inductive ReflexiveTransitiveClosure (R : Set (α × α)) : Set (α × α) where
  | fromR : ∀ x y, R ⟨x, y⟩ → (ReflexiveTransitiveClosure R) ⟨x, y⟩
  | reflexive : ∀ x, (ReflexiveTransitiveClosure R) ⟨x, x⟩
  | transitive :
    ∀ x y z, R ⟨x, y⟩ → R ⟨y, z⟩
    → (ReflexiveTransitiveClosure R) ⟨x, z⟩
end Examples.E2_1_9

-- Section 3, "The rule induction principle"

namespace SyntacticRule
def derivable_subset {X : Set t} (R : Set (SyntacticRule X)) : Set t :=
  { x | Derivation.derives R x }

lemma derivable_subset_is_subset {X : Set t}
  (R : Set (SyntacticRule X))
  : derivable_subset R ⊆ X := by
  intro x x_derivation
  rcases x_derivation with ⟨d⟩
  cases d with
  | ax _ _ => simp
  | with_premises _ _ => simp

lemma in_derivable_subset_iff_derives {X : Set t}
  (R : Set (SyntacticRule X))
  : ∀ x, x ∈ derivable_subset R ↔ Derivation.derives R x := by
  intro x
  constructor
  · intro h
    exact h
  · intro h
    exact h

-- Theorem 3.1, "Rule induction"
theorem rule_induction
  : ∀ (R : Set (SyntacticRule X)),
  (derivable_subset R ∈ Cl R)
  ∧ (∀ S, S ∈ Cl R → derivable_subset R ⊆ S) := by
  intro R
  constructor
  · dsimp [Cl]
    dsimp [closure_conditions_inter]
    dsimp [derivable_subset]
    intro Y h_Y_mem_closure_conditions
    rcases h_Y_mem_closure_conditions with ⟨r, h_rmem, h_Y_r_closure_condition⟩
    rw [← h_Y_r_closure_condition]
    dsimp [closure_condition]
    constructor
    · exact derivable_subset_is_subset R
    · intro premise_derivations
      apply Nonempty.intro
      apply Derivation.with_premises h_rmem
      intro u u_premise
      apply Nonempty.some
      exact premise_derivations u u_premise
  · intro S h_S_mem_closure_conditions
    -- Note that these `change` lines are written to
    -- follow the lecture notes (ish)
    change ∀ v, v ∈ derivable_subset R → v ∈ S
    change ∀ v, Nonempty (Derivation R v) → v ∈ S
    intro v ⟨d⟩
    have h_closure_condition :
      ∀ (r : SyntacticRule X) (h_rmem : r ∈ R),
      (∀ u, u ∈ r.premise_values → u ∈ S)
      → r.conclusion_value ∈ S
      := by
      have h_S_mem_closure_conditions' :
        ∀ (r : SyntacticRule X), r ∈ R →
          S ⊆ X ∧
            ((∀ u, u ∈ r.premise_values → u ∈ S) → r.conclusion_value ∈ S) := by
        simpa [Cl, closure_conditions_inter, closure_condition]
          using h_S_mem_closure_conditions
      intro r h_rmem h
      exact (h_S_mem_closure_conditions' r h_rmem).right h
    induction d with
    | @ax r h_rmem h_r_axiom =>
      apply h_closure_condition r h_rmem
      intro u h_umem
      dsimp [is_axiom] at h_r_axiom
      apply List.nil_of_isEmpty at h_r_axiom
      have h_r_premise_values_eq_nil : r.premise_values = [] := by
        exact (SyntacticRule.premise_values_eq_nil_if_premises_eq_nil r h_r_axiom)
      rw [h_r_premise_values_eq_nil] at h_umem
      exfalso
      apply List.not_mem_nil
      exact h_umem
    | @with_premises r h_rmem h_premises ih =>
      apply h_closure_condition r h_rmem
      intro u h_umem
      exact ih u h_umem

theorem rule_induction_as_subset
  : ∀ (R : Set (SyntacticRule X)),
  derivable_subset R = Set.sInter (Cl R) := by
  intro R
  have ⟨h_X_in_Cl, h_X_min⟩ := rule_induction R
  apply Set.Subset.antisymm
  · exact Set.subset_sInter h_X_min
  · exact Set.sInter_subset_of_mem h_X_in_Cl

-- Example 3.2, "Application of rule induction"
namespace Examples.E3_2
open Examples.E2_1_8

abbrev L := ExampleLanguage

def count {symbols : Finset Char} (s : Strings symbols) (x : Alphabet symbols) : ℕ :=
  let ⟨x, _⟩ := x
  List.countP (fun ⟨y, _⟩ => y = x) s

def P (u : Strings {'a', 'b'}) : Prop :=
  count u ⟨'a', by simp⟩ = count u ⟨'b', by simp⟩

example : ∀ u, Derivation L u → P u := by
  let S := { u | P u }
  intro u d
  suffices S ∈ Cl L by
    have h : derivable_subset L ⊆ S := by
      apply (rule_induction L).right
      exact this
    have h_in_derivable_subset : u ∈ derivable_subset L := by
      apply (in_derivable_subset_iff_derives L u).mp
      exact Nonempty.intro d
    have h_u_in_S : u ∈ S := h h_in_derivable_subset
    simpa [S] using h_u_in_S
  apply in_Cl_if_closed L S
  · intro x hx
    simp [set_of_type]
  · intro r r_in_L h_premises_in_S
    rcases Set.mem_sUnion.mp r_in_L with ⟨W, hW_mem, h_r_mem_W⟩
    have hW_cases := by simpa [ExampleLanguage] using hW_mem
    rcases hW_cases with hW0 | hW1 | hW2 | hW3
    · cases hW0
      have hr : r = { premises := [], conclusion := ⟨ε, by simp⟩ } := by
        simpa [Set.mem_singleton_iff] using h_r_mem_W
      subst hr
      -- Axiom rule: ε has equally many a's and b's.
      simp [S, P, count]
    · cases hW1
      rcases (by simpa [Set.mem_setOf_eq] using h_r_mem_W) with ⟨w, hr⟩
      subst hr
      have hw_in_S : w ∈ S := h_premises_in_S w (by simp)
      have hPw : P w := by simpa [S] using hw_in_S
      change P (Strings.concat [⟨'a', by simp⟩] (Strings.concat w [⟨'b', by simp⟩]))
      dsimp [P, count] at hPw ⊢
      simp [List.countP_append, hPw]
    · cases hW2
      rcases (by simpa [Set.mem_setOf_eq] using h_r_mem_W) with ⟨w, hr⟩
      subst hr
      have hw_in_S : w ∈ S := h_premises_in_S w (by simp)
      have hPw : P w := by simpa [S] using hw_in_S
      change P (Strings.concat [⟨'b', by simp⟩] (Strings.concat w [⟨'a', by simp⟩]))
      dsimp [P, count] at hPw ⊢
      simp [List.countP_append, hPw]
    · cases hW3
      rcases (by simpa [Set.mem_setOf_eq] using h_r_mem_W) with ⟨w, v, hr⟩
      subst hr
      have hw_in_S : w ∈ S := h_premises_in_S w (by simp)
      have hv_in_S : v ∈ S := h_premises_in_S v (by simp)
      have hPw : P w := by simpa [S] using hw_in_S
      have hPv : P v := by simpa [S] using hv_in_S
      change P (Strings.concat w v)
      dsimp [P, count] at hPw hPv ⊢
      simp [List.countP_append, hPw, hPv]
end Examples.E3_2

end SyntacticRule

end FormalLanguagesAndAutomata
