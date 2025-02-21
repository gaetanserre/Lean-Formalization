/-
 - Created in 2024 by Gaëtan Serré
 -/

import Mathlib.Order.Filter.Ultrafilter.Defs
open Classical

def Pxor (A B : Prop) := (A ∨ B) ∧ ¬(A ∧ B)

/--
- A finitely additive {0, 1}-measure.
-/
structure finitely_additive_measure (α : Type*) where
  f : Set α → ℕ
  zero_one : ∀ A, f A = 0 ∨ f A = 1
  zero_empty : f ∅ = 0
  one_univ : f Set.univ = 1
  disjoint_add : ∀ ⦃A B⦄, A ∩ B = ∅ → f (A ∪ B) = f A + f B

/--
- Indicator function over an ultrafilter
-/
noncomputable def ultrafilter_measure {α : Type*} (𝒰 : Ultrafilter α) := λ A ↦ if A ∈ 𝒰 then 1 else 0

/--
- A set of sets induced by a finitely additive {0, 1}-measure.
-/
def measure_ultrafilter {α : Type*} (m : finitely_additive_measure α) := {A | m.f A = 1}
