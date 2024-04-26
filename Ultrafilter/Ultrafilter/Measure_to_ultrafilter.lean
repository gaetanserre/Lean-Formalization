/-
 - Created in 2024 by Gaëtan Serré
 -/

import Ultrafilter.Defs

set_option maxHeartbeats 1000000
set_option trace.Meta.Tactic.simp.rewrite true

/-
Here, we show that a finitely additive {0, 1}-measure defines an ultrafilter.
-/

variable {α : Type}

lemma notin_imp_zero (m : finitely_additive_measure α) : ∀ ⦃E⦄, E ∉ measure_ultrafilter m → m.f E = 0 := by
  intro E E_notin
  have zero_or_one : m.f E = 0 ∨ m.f E = 1 := m.zero_one E
  cases zero_or_one with
  | inl => assumption
  | inr => contradiction

lemma univ_sets (m : finitely_additive_measure Ω) : Set.univ ∈ measure_ultrafilter m := m.one_univ

lemma sets_of_superset (m : finitely_additive_measure α) {x y : Set α} : x ∈ measure_ultrafilter m → x ⊆ y → y ∈ measure_ultrafilter m := by
  -- The proof here is to show that y = x ∪ y \ x and that these two sets are disjoint.
  intro x_in x_ss_y
  have m_y : m.f y = 1 := by {
    rw [←Set.union_diff_cancel' (λ ⦃a⦄ a ↦ a) x_ss_y]
    have disjoint_add := m.disjoint_add (Set.inter_diff_self x y)
    rw [x_in] at disjoint_add
    rw [disjoint_add]
    have m_yx : m.f (y \ x) = 0 := by {
      by_contra h; push_neg at h
      cases m.zero_one (y \ x) with
      | inl =>
        contradiction
      | inr h_myx =>
        rw [h_myx, show 1 + 1 = 2 by rfl] at disjoint_add
        cases m.zero_one (x ∪ y \ x) with
        | inl =>
          linarith
        | inr =>
          linarith
    }
    rw [m_yx]
  }
  exact m_y

lemma inter_sets (m : finitely_additive_measure α) {x y : Set α} : x ∈ measure_ultrafilter m → y ∈ measure_ultrafilter m → x ∩ y ∈ measure_ultrafilter m := by
  -- The idea of the proof is to show that, if m(x ∩ y) = 0, then m(x ∪ y) = m(x \ y) + m(x ∩ y) + m(y \ x) = 1 + 0 + 1 = 2, which contradicts the definition of m.

  intro x_in y_in
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

  have diff_eq_one : ∀ ⦃A B⦄, m.f (A ∩ B) = 0 → m.f A = 1 → m.f (A \ B) = 1 := by {
    intro A B zero_inter m_A
    rw [←Set.diff_union_inter A B, m.disjoint_add (diff_disjoint_inter A B), zero_inter] at m_A
    assumption
  }

  have m_inter_zero : m.f (x ∩ y) = 0 := by {
    cases m.zero_one (x ∩ y) with
    | inl h_zero => assumption
    | inr h_one =>
      have : x ∩ y ∈ measure_ultrafilter m := h_one
      contradiction
  }
  have m_zero_inter : m.f (y ∩ x) = 0 := by rwa [Set.inter_comm x y] at m_inter_zero

  have x_diff_y_eq_one := diff_eq_one m_inter_zero x_in
  have y_diff_x_eq_one := diff_eq_one m_zero_inter y_in

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

    rw [m.disjoint_add first_disjoint]

    have second_disjoint : (x ∩ y) ∩ (y \ x) = ∅ := by {
      rw [←Set.inter_comm (y \ x) (x ∩ y)]
      rw [Set.inter_comm x y]
      exact diff_disjoint_inter y x
    }

    rw [m.disjoint_add second_disjoint]
    rw [m_inter_zero, x_diff_y_eq_one, y_diff_x_eq_one]
  }
  cases m.zero_one (x ∪ y) with
  | inl h_zero => linarith
  | inr h_one => linarith

lemma not_contains_empty (m : finitely_additive_measure α) : ∅ ∉ measure_ultrafilter m := by
  by_contra h
  have h : m.f ∅ = 1 := h
  rw [m.zero_empty] at h
  contradiction

lemma complement (m : finitely_additive_measure α) : ∀ s, sᶜ ∉ measure_ultrafilter m ↔ s ∈ measure_ultrafilter m := by
  intro s
  have m_sc_zero : ∀ ⦃s⦄, s ∉ measure_ultrafilter m → m.f s = 0 := by {
      intro s s_inn
      cases m.zero_one s with
      | inl hl => assumption
      | inr hr => contradiction
    }
  have : s ∩ sᶜ = ∅ := Set.inter_compl_self s

  have m_s_sc_one : m.f (s ∪ sᶜ) = 1 := by {
      rw [Set.union_compl_self s, m.one_univ]
  }

  constructor
  · intro sc_inn
    rwa [m.disjoint_add (Set.inter_compl_self s), m_sc_zero sc_inn] at m_s_sc_one
  intro s_in
  rw [m.disjoint_add (Set.inter_compl_self s), s_in] at m_s_sc_one
  have : m.f sᶜ = 0 := by linarith
  by_contra h
  have : m.f sᶜ = 1 := h
  linarith

-- The previous lemmas allow to implement an ultrafilter given only a finitely additive {0, 1}-measure.
def f (m : finitely_additive_measure α) : Filter α := {
  sets := measure_ultrafilter m
  univ_sets := univ_sets m
  sets_of_superset := sets_of_superset m
  inter_sets := inter_sets m
}

def 𝒰 (m : finitely_additive_measure α) : Ultrafilter α := Ultrafilter.ofComplNotMemIff (f m) (complement m)
