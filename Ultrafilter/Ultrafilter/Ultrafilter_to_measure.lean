/-
 - Created in 2024 by Gaëtan Serré
 -/

import Ultrafilter.Defs

set_option maxHeartbeats 1000000
set_option trace.Meta.Tactic.simp.rewrite true

/-
Here, we show that the `ultrafilter_measure`, which is the indicator function over a ultrafilter, defines a finitely additive {0, 1}-measure.
-/

variable {α : Type} {X : Set α}

lemma zero_one (U : ultrafilter X) : (∀ A ⊆ Ω, ultrafilter_measure U A = 0 ∨ ultrafilter_measure U A = 1) := by
  intro A _
  unfold ultrafilter_measure
  split
  · exact Or.inr (rfl)
  exact Or.inl (rfl)

lemma finitely_additive (U : ultrafilter X) : ∀ A B, A ⊆ X → B ⊆ X → A ∩ B = ∅ → ultrafilter_measure U (A ∪ B) = ultrafilter_measure U A + ultrafilter_measure U B := by
  let m := ultrafilter_measure U
  intro A B A_X B_X h_disjoint
  have not_in_U : A ∩ B ∉ U.sets := by {
    rw [h_disjoint]
    exact U.not_contains_empty
  }
  have : m (A ∩ B) = 0 := by {
    rw [show m (A ∩ B) = ultrafilter_measure U (A ∩ B) by rfl]
    unfold ultrafilter_measure
    split
    · contradiction
    rfl
  }

  -- Suppose A ∪ B ∉ U. It follows that A, B ∉ U. Then, m(A ∪ B) = m(A) + m(B) = 0
  by_cases h_notin : A ∪ B ∉ U.sets
  · have ss_of_union : ∀ E ⊆ A ∪ B, E ∉ U.sets := by {
      intro E hE
      by_contra h_contra
      exact h_notin (U.sets_of_superset h_contra (Set.union_subset A_X B_X) hE)
    }
    have A_notin_U : A ∉ U.sets := ss_of_union A (by simp)
    have B_notin_U : B ∉ U.sets := ss_of_union B (by simp)
    have not_in_U_eq_0 : ∀ E ∉ U.sets, ultrafilter_measure U E = 0 := by {
      intro E hE
      unfold ultrafilter_measure
      split
      · contradiction
      rfl
    }
    rw [not_in_U_eq_0 _ h_notin, not_in_U_eq_0 _ A_notin_U, not_in_U_eq_0 _ B_notin_U]

  -- Now, if A ∪ B ∈ U, we show that A ∈ U xor B ∈ U. Then, m(A ∪ B) = m(A) + m(B) = 1
  push_neg at h_notin
  have h_in := h_notin

  have A_xor_B_in_U : Pxor (A ∈ U.sets) (B ∈ U.sets) := by {
    unfold Pxor
    by_contra h_xor; push_neg at h_xor
    by_cases h_A_or_B_in : A ∈ U.sets ∨ B ∈ U.sets
    · obtain ⟨A_in, B_in⟩ := h_xor h_A_or_B_in
      exact not_in_U (U.inter_sets A_in B_in)
    push_neg at h_A_or_B_in
    obtain ⟨A_notin, B_notin⟩ := h_A_or_B_in

    obtain ⟨A_or_XA, _⟩ := U.complement _ A_X
    cases A_or_XA with
    | inl A_in => exact A_notin A_in
    | inr XA_in =>
      have inter_sets : (X \ A) ∩ (A ∪ B) ∈ U.sets := U.inter_sets XA_in h_in
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
      have B_in : B ∈ U.sets := by {
        exact U.sets_of_superset inter_sets B_X (Set.diff_subset B A)
      }
      exact B_notin B_in
  }

  have m_in : ∀ E ∈ U.sets, ultrafilter_measure U E = 1 := by {
      intro E Ein
      unfold ultrafilter_measure
      split <;> rfl
  }

  have m_notin : ∀ E ∉ U.sets, ultrafilter_measure U E = 0 := by {
    intro E Enotin
    unfold ultrafilter_measure
    split
    · contradiction
    rfl
  }

  by_cases hA : A ∈ U.sets

  · obtain ⟨_, b_notin⟩ := A_xor_B_in_U
    push_neg at b_notin
    specialize b_notin hA

    rw [m_in (A ∪ B) h_in, m_in A hA, m_notin B b_notin]

  obtain ⟨A_or_B, _⟩ := A_xor_B_in_U
  cases A_or_B with
  | inl hl => exact hA.elim hl
  | inr hB =>
    rw [m_in (A ∪ B) h_in, m_in B hB, m_notin A hA]

lemma zero_empty (U : ultrafilter X) : ultrafilter_measure U ∅ = 0 := by
  unfold ultrafilter_measure
  split
  · have := U.not_contains_empty
    contradiction
  rfl

lemma one_univ (U : ultrafilter X) : ultrafilter_measure U X = 1 := by
  unfold ultrafilter_measure
  split
  · rfl
  have := U.univ_sets
  contradiction

-- The previous lemmas allow to implement a finitely additive {0, 1}-measure given only a ultrafilter.
variable (U : ultrafilter X)
noncomputable def m : finitely_additive_measure X := {
  f := ultrafilter_measure U
  zero_one := λ A ↦ zero_one U A
  zero_empty := zero_empty U
  one_univ := one_univ U
  disjoint_add := finitely_additive U
}
