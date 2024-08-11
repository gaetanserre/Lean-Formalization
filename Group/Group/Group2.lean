/-
  Created in 2024 by Gaëtan Serré
-/


import Mathlib

set_option maxHeartbeats 5000000

open Set Function

variable {α : Type} {A : Set α} (hA : A.Infinite)

example : (A ×ˢ A).Infinite := Infinite.prod_left hA hA.nonempty

namespace Set

/-- Set of finite powersets. -/
def fin_powerset {α : Type} (A : Set α) := {S | S ∈ 𝒫 A ∧ S.Finite}

def symm_diff {α : Type} (A B : Set α) := (A ∩ Bᶜ) ∪ (Aᶜ ∩ B)

end Set

theorem card_fin_powerset : ∃ (f : A → A.fin_powerset), f.Bijective := by sorry

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


lemma f_nonempty : {(f : A → A.fin_powerset) | Bijective f}.Nonempty := card_fin_powerset

noncomputable def f : A → A.fin_powerset := f_nonempty.some

lemma f_mem : f ∈ {(f : A → A.fin_powerset) | Bijective f} := f_nonempty.some_mem

lemma f_has_inv : ∃ (g : A.fin_powerset → A), LeftInverse g f ∧ RightInverse g f :=
  bijective_iff_has_inverse.mp f_mem

lemma f_inv_nonempty : {(g : A.fin_powerset → A) | LeftInverse g f ∧ RightInverse g f}.Nonempty :=
  f_has_inv

noncomputable def f_inv : A.fin_powerset → A := f_inv_nonempty.some

noncomputable instance : HMul A A A where
  hMul := fun a b ↦ f_inv (f a * f b)

noncomputable instance : One A where
  one := f_inv 1

noncomputable instance : Inv A.fin_powerset where
  inv := fun a ↦ f_inv (f a)⁻¹
