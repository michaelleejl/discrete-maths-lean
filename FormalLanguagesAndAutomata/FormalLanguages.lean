import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Basic

namespace FormalLanguagesAndAutomata.FormalLanguages


-- Definition 1.1
def Alphabet {t} (symbols : Finset t) : Type :=
  { x : t // x ∈ symbols }

-- For example, this is an alphabet of characters, which has three symbols: 'a', 'b', and 'c'.
example : Type := Alphabet {'a', 'b', 'c'}

-- Definition 1.2
def String {t} (symbols : Finset t) n := Vector (Alphabet symbols) n

example : String {'a', 'b', 'c'} 3 :=
  Vector.mk
    #[⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩]
    rfl

def Strings {t} (symbols : Finset t) := Σ n, String symbols n

example : Strings {'a', 'b', 'c'} :=
  ⟨
    3,
    Vector.mk
      #[⟨'a', by simp⟩, ⟨'b', by simp⟩, ⟨'c', by simp⟩]
      rfl
  ⟩

-- Definition 1.3
def string_concat {t} {symbols : Finset t} {n_s₁ n_s₂}
    (s₁ : String symbols n_s₁) (s₂ : String symbols n_s₂)
    : String symbols (n_s₁ + n_s₂) :=
  Vector.append s₁ s₂

notation s₁ " @ " s₂ => string_concat s₁ s₂

example : String {'a', 'b', 'c'} 4 :=
  (Vector.mk #[⟨'a', by simp⟩, ⟨'b', by simp⟩] rfl) @
  (Vector.mk #[⟨'c', by simp⟩, ⟨'c', by simp⟩] rfl)


end FormalLanguagesAndAutomata.FormalLanguages
