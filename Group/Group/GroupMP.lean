/-
  Created in 2024 by Gaëtan Serré
-/


import Mathlib

set_option maxHeartbeats 5000000

open Set Function

variable {α : Type} {A : Set α} (hA : A.Infinite)

namespace Group

noncomputable def bijection {α β : Type*} [Group α] (f : β → α) (hf : f.Bijective) : Group β := by
  have f_inv_nonempty : {(g : α → β) | LeftInverse g f ∧ RightInverse g f}.Nonempty :=
    bijective_iff_has_inverse.mp hf
  let f_inv := f_inv_nonempty.some
  have hf_inv1 : ∀ a, f_inv (f a) = a := fun a ↦ f_inv_nonempty.some_mem.1 a
  have hf_inv2 : ∀ a, f (f_inv a) = a := fun a ↦ f_inv_nonempty.some_mem.2 a

  let _ : One β := {one := f_inv 1}
  let _ : HMul β β β := {hMul := fun a b ↦ f_inv (f a * f b)}
  let _ : Inv β := {inv := fun a ↦ f_inv (f a)⁻¹}

  exact {
    mul := fun a b ↦ f_inv (f a * f b)
    mul_assoc := by
      intro a b c
      rw [show a * b = f_inv (f a * f b) by rfl]
      rw [show b * c = f_inv (f b * f c) by rfl]
      rw [show f_inv (f a * f b) * c = f_inv (f (f_inv (f a * f b)) * f c) by rfl]
      rw [show a * f_inv (f b * f c) = f_inv (f a * (f (f_inv (f b * f c)))) by rfl]
      repeat rw [hf_inv2]
      suffices f a * f b * f c = f a * (f b * f c) by exact congrArg f_inv this
      exact mul_assoc (f a) (f b) (f c)
    one_mul := by
      intro a
      rw [show 1 * a = f_inv (f 1 * f a) by rfl]
      rw [show (1 : β) = f_inv 1 by rfl]
      rw [hf_inv2, LeftCancelMonoid.one_mul]
      exact hf_inv1 a
    mul_one := by
      intro a
      rw [show a * 1 = f_inv (f a * f 1) by rfl]
      rw [show (1 : β) = f_inv 1 by rfl]
      rw [hf_inv2, LeftCancelMonoid.mul_one]
      exact hf_inv1 a
    inv := fun a ↦ f_inv (f a)⁻¹
    mul_left_inv := by
      intro a
      rw [show a⁻¹ = f_inv (f a)⁻¹ by rfl]
      rw [show f_inv (f a)⁻¹ * a = f_inv (f (f_inv (f a)⁻¹) * f a) by rfl]
      rw [hf_inv2, inv_mul_self]
      rfl
  }

end Group

namespace Set

/-- Set of finite powersets. -/
def fin_powerset {α : Type} (A : Set α) := {S | S ∈ 𝒫 A ∧ S.Finite}

def symm_diff {α : Type} (A B : Set α) := (A ∩ Bᶜ) ∪ (Aᶜ ∩ B)

end Set

lemma symm_diff_mem {C D : A.fin_powerset} : C.1.symm_diff D.1 ∈ A.fin_powerset :=
  ⟨
  union_subset (fun _ h ↦ C.2.1 (inter_subset_left h)) (fun _ h ↦ D.2.1 (inter_subset_right h)),
  Finite.union (Finite.inter_of_left C.2.2 _) (Finite.inter_of_right D.2.2 _)
  ⟩

lemma emptyset_ss_powerset : ∅ ∈ A.fin_powerset := ⟨empty_subset A, finite_empty⟩

lemma symm_diff_eq {α : Type} {C D : Set α} : (C ∩ Dᶜ) ∪ (Cᶜ ∩ D) = (C ∪ D) ∩ (Cᶜ ∪ Dᶜ) := by
  ext e
  constructor
  · intro h
    cases h with
    | inl h =>
      rcases h with ⟨hC, hDc⟩
      exact ⟨mem_union_left D hC, mem_union_right Cᶜ hDc⟩
    | inr h =>
      rcases h with ⟨hCc, hD⟩
      exact ⟨mem_union_right C hD, mem_union_left Dᶜ hCc⟩
  rintro ⟨hCD, hCcDc⟩
  cases hCD with
  | inl hC =>
    cases hCcDc with
    | inl hCc =>
      contradiction
    | inr hDc =>
      left
      exact ⟨hC, hDc⟩
  | inr hD =>
    cases hCcDc with
    | inl hCc =>
      right
      exact ⟨hCc, hD⟩
    | inr hDc =>
      contradiction

instance : HMul A.fin_powerset A.fin_powerset A.fin_powerset where
  hMul := fun a b ↦ ⟨a.1.symm_diff b.1, symm_diff_mem⟩

instance : One A.fin_powerset where
  one := ⟨∅, emptyset_ss_powerset⟩

instance : Inv A.fin_powerset where
  inv := fun a ↦ a

instance : Group A.fin_powerset where
  mul := fun a b ↦ ⟨a.1.symm_diff b.1, symm_diff_mem⟩
  mul_assoc := by
    intro R S T
    refine SetCoe.ext ?_
    rw [show (R * S * T).1 = (R.1.symm_diff S.1).symm_diff T.1 by rfl]
    rw [show (R * (S * T)).1 = R.1.symm_diff (S.1.symm_diff T.1) by rfl]
    unfold symm_diff

    -- Left hand side
    rw (config := {occs := .pos [2]}) [@symm_diff_eq α R.1 S.1]
    rw [union_inter_distrib_right (R.1 ∩ (S.1)ᶜ) ((R.1)ᶜ ∩ S.1) (T.1)ᶜ]
    rw [compl_inter (R.1 ∪ S.1) ((R.1)ᶜ ∪ (S.1)ᶜ)]
    rw [compl_union R.1 S.1, compl_union (R.1)ᶜ (S.1)ᶜ]
    repeat rw [compl_compl]
    rw [union_inter_distrib_right ((R.1)ᶜ ∩ (S.1)ᶜ) (R.1 ∩ S.1) T.1]

    -- Right hand side
    rw (config := {occs := .pos [1]}) [@symm_diff_eq α S.1 T.1]
    rw [inter_union_distrib_left (R.1)ᶜ (S.1 ∩ (T.1)ᶜ) ((S.1)ᶜ ∩ T.1)]
    rw [(inter_assoc (R.1)ᶜ S.1 (T.1)ᶜ).symm, (inter_assoc (R.1)ᶜ (S.1)ᶜ T.1).symm]
    rw [compl_inter (S.1 ∪ T.1) ((S.1)ᶜ ∪ (T.1)ᶜ)]
    rw [compl_union S.1 T.1, compl_union (S.1)ᶜ (T.1)ᶜ]
    repeat rw [compl_compl]
    rw [inter_union_distrib_left R.1 ((S.1)ᶜ ∩ (T.1)ᶜ) (S.1 ∩ T.1)]
    rw [(inter_assoc R.1 (S.1)ᶜ (T.1)ᶜ).symm, (inter_assoc R.1 S.1 T.1).symm]

    -- Assoc/Comm union
    set A := R.1 ∩ (S.1)ᶜ ∩ (T.1)ᶜ
    set B := (R.1)ᶜ ∩ S.1 ∩ (T.1)ᶜ
    set C := (R.1)ᶜ ∩ (S.1)ᶜ ∩ T.1
    set D := R.1 ∩ S.1 ∩ T.1
    rw [(union_assoc (A ∪ B) C D).symm, (union_assoc (A ∪ D) B C).symm]
    rw [union_right_comm A D B, union_right_comm (A ∪ B) C D]

  one := ⟨∅, emptyset_ss_powerset⟩
  one_mul := by
    intro a
    refine SetCoe.ext ?_
    rw [show ((1 : A.fin_powerset) * a).1 = (∅ : Set α).symm_diff a.1 by rfl]
    unfold symm_diff
    rw [empty_inter, compl_empty, univ_inter]
    exact empty_union a.1
  mul_one := by
    intro a
    refine SetCoe.ext ?_
    rw [show (a * 1).1 = a.1.symm_diff ∅ by rfl]
    unfold symm_diff
    rw [compl_empty, inter_univ, inter_empty, union_empty]
  inv := fun a ↦ a
  mul_left_inv := by
    intro a
    refine SetCoe.ext ?_
    rw [show (a⁻¹ * a).1 = a.1.symm_diff a.1 by rfl]
    rw [show (1 : A.fin_powerset).1 = ∅ by rfl]
    unfold symm_diff
    rw [inter_compl_self, compl_inter_self, empty_union]

theorem card_fin_powerset : ∃ (f : A → A.fin_powerset), f.Bijective := by sorry

lemma f_nonempty : {(f : A → A.fin_powerset) | Bijective f}.Nonempty := card_fin_powerset

noncomputable def f : A → A.fin_powerset := f_nonempty.some

noncomputable instance : Group A := Group.bijection f f_nonempty.some_mem
