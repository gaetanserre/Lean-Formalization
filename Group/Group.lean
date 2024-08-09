/-
  Created in 2024 by Gaëtan Serré
-/


import Mathlib
import Mathlib.Data.Prod.Lex

set_option maxHeartbeats 1000000

open Set Function Prod.Lex

variable {α β : Type*} (A B : Set α) [LT α] (hB : B.IsWF)

variable [G : Group (A ∪ B).Elem]

def injA {A B : Set α} (a : A) : (A ∪ B).Elem := ⟨a.1, mem_union_left B a.2⟩
def injB {A B : Set α} (b : B) : (A ∪ B).Elem := ⟨b.1, mem_union_right A b.2⟩

lemma no_inj_imp_group_union_right (no_injection : ∀ (f : B → A), ¬Injective f) :
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

variable (no_injection : ∀ (f : B → A), ¬ Injective f)

def AB (a : A) := {b : B | ((injA a) * (injB b)).1 ∈ B}

example : ∀ (a : A), (AB A B a).Nonempty :=
  fun a ↦ no_inj_imp_group_union_right A B no_injection a

def S (a : A) := {p : (B × B) | p.1 ∈ (@AB α A B G a) ∧ ((injA a) * (injB p.1)).1 = p.2.val}

instance : LT (α × α) where
  lt := Prod.Lex (· < ·) (· < ·)

lemma S_WF (a : A) : (S A B a).IsWF := by
  have univ_wf : univ.IsWF := WellFounded.onFun (WellFounded.prod_lex hB hB)
  exact IsWF.mono univ_wf (fun _ _ => trivial)

lemma S_ne : ∀ a, (S A B a).Nonempty := by sorry

noncomputable def f := fun (a : A) ↦ (WellFounded.min (S_WF A B hB a) univ (nonempty_iff_univ_nonempty.1 (S_ne A B a).to_subtype)).1

lemma f_mem (a : A) : f A B hB a ∈ (S A B a) := (WellFounded.min (S_WF A B hB a) univ (nonempty_iff_univ_nonempty.1 (S_ne A B a).to_subtype)).2
