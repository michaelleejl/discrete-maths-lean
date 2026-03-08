import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Vector.Defs
import Mathlib.Algebra.Group.Defs

-- TODO - instead of having this overarching namespace, have namespaces
--        for each type of thing, which should contain the functions and theorems for it

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
structure SyntacticRule (t : Type) where
  premises : List t
  conclusion : t

namespace SyntacticRule

def is_axiom (R : SyntacticRule t) : Prop :=
  List.isEmpty R.premises

-- Example 2.1.4.2, "Syntactic rules for forming natural numbers"
namespace Examples.E2_1_4_2

def zero : SyntacticRule ℝ :=
  { premises := [], conclusion := 0 }

def succ (x : ℝ) : SyntacticRule ℝ :=
  { premises := [x], conclusion := x + 1 }

end Examples.E2_1_4_2

-- Definition 2.1.4.3, "The closure condition denoted by a syntactic rule"
-- TODO

-- TODO - continue syntactic rule stuff

end SyntacticRule

-- TODO - should we do anything about how they describe notation
--        and stuff about rule induction, since we can just use
--        `inductive` for the formalization later on

-- Example 2.1.8, "A syntactic presentation of a formal language"
namespace Examples.E2_1_8
inductive ExampleLanguage : FormalLanguage {'a', 'b', 'c'} where
  | empty : ExampleLanguage ε
  | aub :
    ∀ u,
    ExampleLanguage u
    → ExampleLanguage
      (Strings.concat [⟨'a', by simp⟩]
        (Strings.concat u
          [⟨'b', by simp⟩]))
  | bua :
    ∀ u,
    ExampleLanguage u
    → ExampleLanguage
      (Strings.concat [⟨'b', by simp⟩]
        (Strings.concat u
          [⟨'a', by simp⟩]))
  | uv :
    ∀ u v,
    ExampleLanguage u → ExampleLanguage v
    → ExampleLanguage (Strings.concat u v)
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
