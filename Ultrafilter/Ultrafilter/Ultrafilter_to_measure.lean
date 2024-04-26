/-
 - Created in 2024 by Gaëtan Serré
 -/

import Ultrafilter.Defs

set_option maxHeartbeats 1000000
set_option trace.Meta.Tactic.simp.rewrite true

/-
Here, we show that the `ultrafilter_measure`, which is the indicator function over an ultrafilter, defines a finitely additive {0, 1}-measure.
-/

variable {α : Type} {X : Set α}

lemma zero_one (𝒰 : ultrafilter X) : (∀ A ⊆ Ω, ultrafilter_measure 𝒰 A = 0 ∨ ultrafilter_measure 𝒰 A = 1) := by
  intro A _
  unfold ultrafilter_measure
  split
  · exact Or.inr (rfl)
  exact Or.inl (rfl)

lemma finitely_additive (𝒰 : ultrafilter X) : ∀ A B, A ⊆ X → B ⊆ X → A ∩ B = ∅ → ultrafilter_measure 𝒰 (A ∪ B) = ultrafilter_measure 𝒰 A + ultrafilter_measure 𝒰 B := by
  let m := ultrafilter_measure 𝒰
  intro A B A_X B_X h_disjoint
  have not_in_U : A ∩ B ∉ 𝒰 := by {
    rw [h_disjoint]
    exact 𝒰.not_contains_empty
  }
  have : m (A ∩ B) = 0 := by {
    rw [show m (A ∩ B) = ultrafilter_measure 𝒰 (A ∩ B) by rfl]
    unfold ultrafilter_measure
    split
    · contradiction
    rfl
  }

  -- Suppose A ∪ B ∉ 𝒰. It follows that A, B ∉ 𝒰. Then, m(A ∪ B) = m(A) + m(B) = 0
  by_cases h_notin : A ∪ B ∉ 𝒰
  · have ss_of_union : ∀ E ⊆ A ∪ B, E ∉ 𝒰 := by {
      intro E hE
      by_contra h_contra
      exact h_notin (𝒰.sets_of_superset h_contra (Set.union_subset A_X B_X) hE)
    }
    have A_notin_U : A ∉ 𝒰 := ss_of_union A (by simp)
    have B_notin_U : B ∉ 𝒰 := ss_of_union B (by simp)
    have not_in_U_eq_0 : ∀ E ∉ 𝒰, ultrafilter_measure 𝒰 E = 0 := by {
      intro E hE
      unfold ultrafilter_measure
      split
      · contradiction
      rfl
    }
    rw [not_in_U_eq_0 _ h_notin, not_in_U_eq_0 _ A_notin_U, not_in_U_eq_0 _ B_notin_U]

  -- Now, if A ∪ B ∈ 𝒰, we show that A ∈ 𝒰 xor B ∈ 𝒰. Then, m(A ∪ B) = m(A) + m(B) = 1
  push_neg at h_notin
  have h_in := h_notin

  have A_xor_B_in_U : Pxor (A ∈ 𝒰) (B ∈ 𝒰) := by {
    unfold Pxor
    by_contra h_xor; push_neg at h_xor
    by_cases h_A_or_B_in : A ∈ 𝒰 ∨ B ∈ 𝒰
    · obtain ⟨A_in, B_in⟩ := h_xor h_A_or_B_in
      exact not_in_U (𝒰.inter_sets A_in B_in)
    push_neg at h_A_or_B_in
    obtain ⟨A_notin, B_notin⟩ := h_A_or_B_in

    obtain ⟨A_or_XA, _⟩ := 𝒰.complement _ A_X
    cases A_or_XA with
    | inl A_in => exact A_notin A_in
    | inr XA_in =>
      have inter_sets : (X \ A) ∩ (A ∪ B) ∈ 𝒰 := 𝒰.inter_sets XA_in h_in
      rw [Set.inter_union_distrib_left (X \ A) A B] at inter_sets
      rw [show (X \ A) ∩ A = ∅ by exact Set.diff_inter_self] at inter_sets
      rw [show ∅ ∪ ((X \ A) ∩ B) = (X \ A) ∩ B by exact Set.empty_union (X \ A ∩ B)] at inter_sets
      have simp_compl : (X \ A) ∩ B = B \ A := by {
        ext e
        constructor
        · intro ein
          obtain ⟨einXA, einB⟩ := (Set.mem_inter_iff e (X \ A) B).mp ein
          have e_notin_A := Set.not_mem_of_mem_diff einXA
          exact Set.mem_diff_of_mem einB e_notin_A
        intro ein
        have einB : e ∈ B := Set.mem_of_mem_diff ein
        have e_notin_A := Set.not_mem_of_mem_diff ein
        have einXA : e ∈ X \ A := Set.mem_diff_of_mem (B_X einB) e_notin_A
        exact Set.mem_inter einXA einB
      }
      rw [simp_compl] at inter_sets
      have : B \ A ⊆ B := Set.diff_subset B A
      have B_in : B ∈ 𝒰 := by {
        exact 𝒰.sets_of_superset inter_sets B_X (Set.diff_subset B A)
      }
      exact B_notin B_in
  }

  have m_in : ∀ E ∈ 𝒰, ultrafilter_measure 𝒰 E = 1 := by {
      intro E Ein
      unfold ultrafilter_measure
      split <;> rfl
  }

  have m_notin : ∀ E ∉ 𝒰, ultrafilter_measure 𝒰 E = 0 := by {
    intro E Enotin
    unfold ultrafilter_measure
    split
    · contradiction
    rfl
  }

  by_cases hA : A ∈ 𝒰

  · obtain ⟨_, b_notin⟩ := A_xor_B_in_U
    push_neg at b_notin
    specialize b_notin hA

    rw [m_in (A ∪ B) h_in, m_in A hA, m_notin B b_notin]

  obtain ⟨A_or_B, _⟩ := A_xor_B_in_U
  cases A_or_B with
  | inl hl => exact hA.elim hl
  | inr hB =>
    rw [m_in (A ∪ B) h_in, m_in B hB, m_notin A hA]

lemma zero_empty (𝒰 : ultrafilter X) : ultrafilter_measure 𝒰 ∅ = 0 := by
  unfold ultrafilter_measure
  split
  · have := 𝒰.not_contains_empty
    contradiction
  rfl

lemma one_univ (𝒰 : ultrafilter X) : ultrafilter_measure 𝒰 X = 1 := by
  unfold ultrafilter_measure
  split
  · rfl
  have := 𝒰.univ_sets
  contradiction

-- The previous lemmas allow to implement a finitely additive {0, 1}-measure given only an ultrafilter.
variable (𝒰 : ultrafilter X)
noncomputable def m : finitely_additive_measure X := {
  f := ultrafilter_measure 𝒰
  zero_one := λ A ↦ zero_one 𝒰 A
  zero_empty := zero_empty 𝒰
  one_univ := one_univ 𝒰
  disjoint_add := finitely_additive 𝒰
}
