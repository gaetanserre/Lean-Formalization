/-
 - Created in 2024 by Gaëtan Serré
 -/

import Ultrafilter.Defs

set_option maxHeartbeats 1000000
set_option trace.Meta.Tactic.simp.rewrite true

/-
Here, we show that a finitely additive {0, 1}-measure defines an ultrafilter.
-/

variable {α : Type} {Ω : Set α}

lemma notin_imp_zero (m : finitely_additive_measure Ω) : ∀ ⦃E⦄, E ⊆ Ω → E ∉ measure_ultrafilter m → m.f E = 0 := by
  intro E E_ss E_notin
  have zero_or_one : m.f E = 0 ∨ m.f E = 1 := m.zero_one E_ss
  have not_in : ¬ ((E ⊆ Ω) ∧ (m.f E = 1)) := E_notin
  push_neg at not_in
  specialize not_in E_ss
  cases zero_or_one with
  | inl => assumption
  | inr => contradiction

lemma membership (m : finitely_additive_measure Ω) : ∀ A ∈ measure_ultrafilter m, A ⊆ Ω := λ _ Ain ↦ Ain.1

lemma univ_sets (m : finitely_additive_measure Ω) : Ω ∈ measure_ultrafilter m := ⟨λ ⦃a⦄ a ↦ a, m.one_univ⟩

lemma sets_of_superset (m : finitely_additive_measure Ω) : ∀ ⦃x y⦄, x ∈ measure_ultrafilter m → y ⊆ Ω → x ⊆ y → y ∈ measure_ultrafilter m := by
  -- The proof here is to show that y = x ∪ y \ x and that these two sets are disjoint.
  intro x y x_in y_ss x_ss_y
  rcases x_in with ⟨x_ss, m_x⟩
  have m_y : m.f y = 1 := by {
    rw [←Set.union_diff_cancel' (λ ⦃a⦄ a ↦ a) x_ss_y]
    have diff_subset : (y \ x) ⊆ Ω := λ ⦃e⦄ e_in ↦ y_ss (Set.mem_of_mem_diff e_in)
    have disjoint_add := m.disjoint_add (x_ss) diff_subset (Set.inter_diff_self x y)
    rw [m_x] at disjoint_add
    rw [disjoint_add]
    have m_yx : m.f (y \ x) = 0 := by {
      by_contra h; push_neg at h
      cases m.zero_one diff_subset with
      | inl =>
        contradiction
      | inr h_myx =>
        rw [h_myx, show 1 + 1 = 2 by rfl] at disjoint_add
        cases m.zero_one (Set.union_subset x_ss diff_subset) with
        | inl =>
          linarith
        | inr =>
          linarith
    }
    rw [m_yx]
  }
  exact ⟨y_ss, m_y⟩

lemma inter_sets (m : finitely_additive_measure Ω) : ∀ ⦃x y⦄, x ∈ measure_ultrafilter m → y ∈ measure_ultrafilter m → x ∩ y ∈ measure_ultrafilter m := by
  -- The idea of the proof is to show that, if m(x ∩ y) = 0, then m(x ∪ y) = m(x \ y) + m(x ∩ y) + m(y \ x) = 1 + 0 + 1 = 2, which contradicts the definition of m.

  intro x y x_in y_in
  rcases x_in with ⟨x_ss, m_x⟩
  rcases y_in with ⟨y_ss, m_y⟩
  by_contra h_inter

  have diff_disjoint_inter : ∀ (A B : Set α), (A \ B) ∩ (A ∩ B) = ∅ := by {
    intro A B
    ext e
    constructor
    · intro e_in
      rcases e_in with ⟨e_in_diff, ⟨_, e_in_B⟩⟩
      have : e ∉ B := Set.not_mem_of_mem_diff e_in_diff
      contradiction
    · intro e_in
      contradiction
  }

  have diff_eq_one : ∀ ⦃A B⦄, A ⊆ Ω → m.f (A ∩ B) = 0 → m.f A = 1 → m.f (A \ B) = 1 := by {
    intro A B A_ss zero_inter m_A

    have inter_subset : A ∩ B ⊆ Ω := λ ⦃e⦄ e_in ↦ A_ss ((Set.inter_subset_left A B) e_in)
    have diff_subset : A \ B ⊆ Ω := λ ⦃e⦄ e_in ↦ A_ss ((Set.diff_subset A B) e_in)

    rw [←Set.diff_union_inter A B, m.disjoint_add diff_subset inter_subset (diff_disjoint_inter A B), zero_inter] at m_A
    assumption
  }

  have inter_subset : x ∩ y ⊆ Ω := λ ⦃e⦄ e_in ↦ x_ss ((Set.inter_subset_left x y) e_in)
  have m_inter_zero : m.f (x ∩ y) = 0 := by {
    cases m.zero_one inter_subset with
    | inl h_zero => assumption
    | inr h_one =>
      have : x ∩ y ∈ measure_ultrafilter m := ⟨inter_subset, h_one⟩
      contradiction
  }
  have m_zero_inter : m.f (y ∩ x) = 0 := by rwa [Set.inter_comm x y] at m_inter_zero

  have x_diff_y_eq_one := diff_eq_one x_ss m_inter_zero m_x
  have y_diff_x_eq_one := diff_eq_one y_ss m_zero_inter m_y

  have m_union_eq_two : m.f (x ∪ y) = 2 := by {
    have split_union : x ∪ y = (x \ y) ∪ (x ∩ y) ∪ (y \ x) := by rw [Set.diff_union_inter x y, Set.union_diff_self.symm]
    rw [split_union]
    rw [Set.union_assoc (x \ y) (x ∩ y) (y \ x)]

    have first_disjoint : (x \ y) ∩ ((x ∩ y) ∪ (y \ x)) = ∅ := by {
    rw [Set.inter_union_distrib_left (x \ y) (x ∩ y) (y \ x)]
    rw [diff_disjoint_inter x y, Set.empty_union (x \ y ∩ (y \ x))]

    ext e
    constructor
    · intro e_in
      rcases e_in with ⟨e_in_x, e_in_y⟩
      exact (Set.not_mem_of_mem_diff e_in_y) (Set.mem_of_mem_diff e_in_x)
    intro h
    contradiction
    }

    have y_diff_x_subset : y \ x ⊆ Ω := λ ⦃e⦄ e_in ↦ y_ss ((Set.diff_subset y x) e_in)
    have x_diff_y_subset : x \ y ⊆ Ω := λ ⦃e⦄ e_in ↦ x_ss ((Set.diff_subset x y) e_in)

    rw [m.disjoint_add x_diff_y_subset (Set.union_subset inter_subset y_diff_x_subset) first_disjoint]

    have second_disjoint : (x ∩ y) ∩ (y \ x) = ∅ := by {
      rw [←Set.inter_comm (y \ x) (x ∩ y)]
      rw [Set.inter_comm x y]
      exact diff_disjoint_inter y x
    }

    rw [m.disjoint_add inter_subset y_diff_x_subset second_disjoint]
    rw [m_inter_zero, x_diff_y_eq_one, y_diff_x_eq_one]
  }
  cases m.zero_one (Set.union_subset x_ss y_ss) with
  | inl h_zero => linarith
  | inr h_one => linarith

lemma not_contains_empty (m : finitely_additive_measure Ω) : ∅ ∉ measure_ultrafilter m := by
  by_contra h
  rcases h with ⟨_, one_empty⟩
  rw [m.zero_empty] at one_empty
  contradiction

lemma complement (m : finitely_additive_measure Ω) : ∀ A ⊆ Ω, Pxor (A ∈ measure_ultrafilter m) (Ω \ A ∈ measure_ultrafilter m) := by
  intro A A_ss
  have disjoint_add := m.disjoint_add A_ss (Set.diff_subset Ω A) (Set.inter_diff_self A Ω)

  have measure_one : m.f (A ∪ (Ω \ A)) = 1 := by {
    rw [Set.union_diff_cancel' (λ ⦃a⦄ a ↦ a) A_ss]
    exact m.one_univ
  }

  unfold Pxor
  by_contra h_xor; push_neg at h_xor
  by_cases h_cases : A ∈ measure_ultrafilter m ∨ Ω \ A ∈ measure_ultrafilter m
  · obtain ⟨⟨_, m_A_one⟩, ⟨_, m_ΩA_one⟩⟩ := h_xor h_cases
    rw [m_A_one, m_ΩA_one, show 1 + 1 = 2 by rfl, measure_one] at disjoint_add
    contradiction
  push_neg at h_cases
  rcases h_cases with ⟨A_notin, ΩA_notin⟩

  rw [notin_imp_zero m A_ss A_notin, notin_imp_zero m (Set.diff_subset Ω A) ΩA_notin, show 0 + 0 = 0 by rfl, measure_one] at disjoint_add
  contradiction

-- The previous lemmas allow to implement an ultrafilter given only a finitely additive {0, 1}-measure.
variable (m : finitely_additive_measure Ω)
def 𝒰 : ultrafilter Ω := {
  sets := measure_ultrafilter m
  membership := membership m
  univ_sets := univ_sets m
  sets_of_superset := λ ⦃x y⦄ ↦ sets_of_superset m x y
  inter_sets := λ ⦃x y⦄ ↦ inter_sets m x y
  not_contains_empty := not_contains_empty m
  complement := complement m
}
