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

@[simp]
theorem premise_values_eq_nil_only_if {X : Set t} (r : SyntacticRule X) :
  r.premise_values = [] → r.premises = [] := by
  intro h
  dsimp [premise_values] at h
  apply List.map_eq_nil_iff.mp at h
  exact h

@[simp]
def conclusion_value {X : Set t} (r : SyntacticRule X) : t :=
  r.conclusion.1

@[simp]
def is_axiom (R : SyntacticRule t) : Prop :=
  List.isEmpty R.premises

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
def ExampleLanguage : FormalLanguageSyntacticPresentation {'a', 'b', 'c'} :=
  Set.sUnion {
    (Set.singleton {premises := [], conclusion := ⟨ε, by simp⟩}),
    { {
        premises := [⟨u, by simp⟩],
        conclusion := ⟨Strings.concat
          [⟨'a', by simp⟩]
          (Strings.concat u [⟨'b', by simp⟩]), by simp⟩}
      | u : Strings {'a', 'b', 'c'} },
    { {
        premises := [⟨u, by simp⟩],
        conclusion := ⟨Strings.concat
          [⟨'b', by simp⟩]
          (Strings.concat u [⟨'a', by simp⟩]), by simp⟩}
      | u : Strings {'a', 'b', 'c'} },
    { {
        premises := [⟨u, by simp⟩, ⟨v, by simp⟩],
        conclusion := ⟨Strings.concat u v, by simp⟩}
      | (u : Strings {'a', 'b', 'c'})
        (v : Strings {'a', 'b', 'c'}) }
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

end FormalLanguagesAndAutomata
