import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Defs

namespace FormalLanguagesAndAutomata.FormalLanguages


-- Definition 1.1, "Alphabet"
def Alphabet {t} (symbols : Finset t) : Type :=
  { x : t // x ∈ symbols }

-- For example, this is an alphabet of characters, which has three symbols: 'a', 'b', and 'c'.
example : Type := Alphabet {'a', 'b', 'c'}

-- Definition 1.2, "String over an alphabet"
def String {t} (symbols : Finset t) n := List.Vector (Alphabet symbols) n

instance {n m : Nat} : HAppend (String α n) (String α m) (String α (n + m)) where
  hAppend
  | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ =>
    ⟨l₁ ++ l₂, by simp [h₁, h₂]⟩

example : String {'a', 'b', 'c'} 3 :=
  ⟨[⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩], rfl⟩

def Strings {t} (symbols : Finset t) := Σ n, String symbols n

instance : Append (Strings α) where
  append
  | ⟨n₁, s₁⟩, ⟨n₂, s₂⟩ =>
    ⟨n₁ + n₂, s₁ ++ s₂⟩

example : Strings {'a', 'b', 'c'} :=
  ⟨
    3,
    ⟨[⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩], rfl⟩
  ⟩

-- Definition 1.3, "Concatenation of strings"
def string_concat_with_length {t} {symbols : Finset t} {n_s₁ n_s₂}
    (s₁ : String symbols n_s₁) (s₂ : String symbols n_s₂)
    : String symbols (n_s₁ + n_s₂) :=
  s₁ ++ s₂

def string_concat {t} {symbols : Finset t} (s₁ : Strings symbols) (s₂ : Strings symbols)
  : Strings symbols :=
    let ⟨n_s₁, s₁⟩ := s₁
    let ⟨n_s₂, s₂⟩ := s₂
    ⟨n_s₁ + n_s₂, string_concat_with_length s₁ s₂⟩

infixl:65 " @ " => string_concat

example : Strings {'a', 'b', 'c'} :=
  ⟨2, ⟨[⟨'a', by simp⟩, ⟨'b', by simp⟩], rfl⟩⟩ @
  ⟨2, ⟨[⟨'c', by simp⟩, ⟨'c', by simp⟩], rfl⟩⟩

def string_empty {t} {symbols : Finset t} : Strings symbols :=
  ⟨0, List.Vector.nil⟩

notation "ε" => string_empty

-- Definition 1.4, "Properties of concatenation"

-- Lemma 1.4ai
lemma eps_concat_neutral {symbols : Finset t} (s : Strings symbols)
  : string_empty @ s = s := by
    dsimp [string_empty, string_concat]
    sorry

-- Lemma 1.4aii
lemma concat_eps_neutral {symbols : Finset t} (s : Strings symbols)
  : s @ ε = s := by
    dsimp [string_empty, string_concat, string_concat_with_length]
    sorry

-- Lemma 1.4b
lemma concat_assoc {symbols : Finset t} (s₁ s₂ s₃ : Strings symbols)
  : (s₁ @ s₂) @ s₃ = s₁ @ (s₂ @ s₃) := by
    sorry

-- TODO


end FormalLanguagesAndAutomata.FormalLanguages
