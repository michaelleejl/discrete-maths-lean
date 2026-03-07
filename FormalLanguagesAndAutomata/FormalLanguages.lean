import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Group.Defs

namespace FormalLanguagesAndAutomata.FormalLanguages


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
@[simp]
def strings_concat {t} {symbols : Finset t}
  (s₁ : Strings symbols) (s₂ : Strings symbols)
  : Strings symbols :=
  List.append s₁ s₂

instance : Append (Strings α) where
  append := strings_concat

@[simp]
theorem strings_append_eq {t} {symbols : Finset t} (s₁ s₂ : Strings symbols) :
  s₁ ++ s₂ = List.append s₁ s₂ := rfl

@[simp]
def string_concat {t} {symbols : Finset t} {n_s₁ n_s₂}
    (s₁ : String symbols n_s₁) (s₂ : String symbols n_s₂)
    : String symbols (n_s₁ + n_s₂) :=
  let (⟨l₁, h₁⟩, ⟨l₂, h₂⟩) := (s₁, s₂)
  ⟨
    l₁ ++ l₂,
    by
      rw [← h₁, ← h₂]
      apply List.length_append
  ⟩

instance : HAppend (String α n) (String α m) (String α (n + m)) where
  hAppend := string_concat

@[simp]
theorem string_append_eq {t} {symbols : Finset t} {n_s₁ n_s₂}
    (s₁ : String symbols n_s₁) (s₂ : String symbols n_s₂) :
  s₁ ++ s₂ = string_concat s₁ s₂ := rfl

-- Lemma 1.4, "Properties of concatenation"

@[simp]
def strings_empty {t} {symbols : Finset t} : Strings symbols :=
  []

@[simp]
def string_empty {t} {symbols : Finset t} : String symbols 0 :=
  ⟨strings_empty, rfl⟩

notation "ε" => strings_empty
notation "ε'" => string_empty

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
  mul := strings_concat
  one_mul := eps_concat
  mul_one := concat_eps
  mul_assoc := concat_assoc

-- Definition 1.6, "Formal language"
def FormalLanguage {t} (symbols : Finset t) :=
  Set (Strings symbols)


end FormalLanguagesAndAutomata.FormalLanguages
