/-
 - Created in 2024 by Gaëtan Serré
 -/

import Mathlib
open Classical

def Pxor (A B : Prop) := (A ∨ B) ∧ ¬(A ∧ B)

structure ultrafilter {α : Type} (X : Set α) where
  sets : Set (Set α)
  membership : ∀ A ∈ sets, A ⊆ X
  univ_sets : X ∈ sets
  sets_of_superset {x y} : x ∈ sets → y ⊆ X → x ⊆ y → y ∈ sets
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets

  not_contains_empty : ∅ ∉ sets
  complement : ∀ A ⊆ X, Pxor (A ∈ sets) (X \ A ∈ sets)

structure finitely_additive_measure {α : Type} (Ω : Set α) where
  f : Set α → ℕ
  zero_one : ∀ ⦃A⦄, A ⊆ Ω → f A = 0 ∨ f A = 1
  zero_empty : f ∅ = 0
  one_univ : f Ω = 1
  disjoint_add : ∀ ⦃A B⦄, A ⊆ Ω → B ⊆ Ω → A ∩ B = ∅ → f (A ∪ B) = f A + f B

noncomputable def ultrafilter_measure {α : Type} {X : Set α} (U : ultrafilter X) := λ A ↦ if A ∈ U.sets then 1 else 0

def measure_ultrafilter {α : Type} {Ω : Set α} (m : finitely_additive_measure Ω) := {U | (U ⊆ Ω) ∧ (m.f U = 1)}
