/-
  Created in 2024 by Gaëtan Serré
-/


import Mathlib

set_option maxHeartbeats 1000000

open Set Function

variable {α β : Type*} {A B : Set α}

variable [G : Group (A ∪ B).Elem]

def injA (a : A) : (A ∪ B).Elem := ⟨a.1, mem_union_left B a.2⟩
def injB (b : B) : (A ∪ B).Elem := ⟨b.1, mem_union_right A b.2⟩

example (no_injection : ∀ (f : B → A), ¬ Injective f) :
    ∀ (a : A), ∃ (b : B), ((injA a) * (injB b)).1 ∈ B := by
  by_contra h; push_neg at h
  rcases h with ⟨a, h⟩
  have union_in_A : ∀ (b : B), ((injA a) * (injB b)).1 ∈ A := by
    intro b
    specialize h b
    cases ((injA a) * (injB b)).2
    · assumption
    contradiction

  let f : B → A := fun b ↦ ⟨((injA a) * (injB b)).1, union_in_A b⟩
  suffices Injective f by specialize no_injection f; contradiction
  intro b₁ b₂ hf
  rw [show f b₁ = ⟨((injA a) * (injB b₁)).1, union_in_A b₁⟩ by rfl] at hf
  rw [show f b₂ = ⟨((injA a) * (injB b₂)).1, union_in_A b₂⟩ by rfl] at hf
  have hf : ((injA a) * (injB b₁)).1 = ((injA a) * (injB b₂)).1 := by
    simp_all only [Subtype.forall, Subtype.mk.injEq]

  have inv_A : (injA a)⁻¹ * ((injA a) * (injB b₁)) = (injA a)⁻¹ * ((injA a) * (injB b₂) ) := by
    exact congrArg (HMul.hMul (injA a)⁻¹) (by ext; exact hf)

  repeat rw [
    (mul_assoc _ _ _).symm,
    inv_mul_self (injA a),
    LeftCancelMonoid.one_mul _
  ] at inv_A

  unfold injB at inv_A
  simp only [Subtype.forall, Subtype.mk.injEq] at inv_A
  exact SetCoe.ext inv_A
