/-
 - Created in 2024 by Gaëtan Serré
 -/

import CayleyGraph.FinGroup

set_option maxHeartbeats 600000

structure Graph (G : Type*) where
  Adj : G → G → Prop
  Connected : Prop
  Acyclic : Prop

namespace Graph
def is_tree {α : Type*} (G : Graph α) := G.Connected ∧ G.Acyclic
end Graph

def CayleyGraph {G : Type*} [Fintype G] [FinGroup G] (X : Set G) : Graph G :=
  {
    Adj := λ g1 g2 ↦ ∃ (F : Formula G X), 0 < F.length ∧ g1 * F.val = g2
    Connected := ∀ g1 g2, g1 ≠ g2 → ∃ (F : Formula G X), 0 < F.length ∧ g1 * F.val = g2
    /-
    For any node `g`, there is no path ((g, g1), ..., (gn, g)) from `g` to `g`. Paths are represented by irreducible Formulas of size >= 1. We use the irreducible property to avoid looking at such Formula: `∀ g' ∈ CG.X, g * [g', g'⁻¹].prod = g`. This kind of Formula gives a trivial path that leads `g` to itself, for any subset `X`. This does not represented a cycle, as reducible Formulas contain steps that cancel each other out in pairs.
    -/
    Acyclic := ∀ g, ∀ (F : Formula G X), 0 < F.length ∧ F.irreducible → g * F.val ≠ g
  }

variable {G : Type*} [Fintype G] [FinGroup G]  [Inhabited G] (X : Set G)
variable (G' : Subgroup G)

/--
We show that, given an irreducible Formula (a path) of size `> 1`, then two consecutive steps never cancel each other out, i.e., given any node `g`, we never go back to `g` directly after moving from it.
-/
example (F : Formula G X) (F_len : 1 < F.length) (F_irr : F.irreducible) : ∀ (g : G), ∀ (i : Fin F.length), g * F.get i * F.get (i + {val:=1, isLt:=F_len}) ≠ g := by
  intro g i
  unfold Formula.irreducible at F_irr
  split at F_irr
  · specialize F_irr i
    by_contra h_contra
    rw [show g * F.get i * F.get (i + {val:=1, isLt:=F_len}) = g * (F.get i * F.get (i + {val:=1, isLt:=F_len})) by exact mul_assoc _ _ _] at h_contra
    exact F_irr (mul_right_eq_self.mp h_contra)
  contradiction

/--
The action of a Subgroup `G'` of `G` on the Cayley graph formed by `G` and `X`
-/
def group_action {G : Type*} [Fintype G] [FinGroup G] {G' : Subgroup G}
  (X : Set G) (g' : G') : Graph G :=
    {
      Adj := λ g1 g2 ↦ (CayleyGraph X).Adj (g1 * g') (g2 * g')
      Connected := ∀ g1 g2, g1 ≠ g2 → ∃ (F : Formula G X), 0 < F.length ∧ g1 * g' * F.val = g2 * g'
      Acyclic := ∀ g, ∀ (F : Formula G X), 0 < F.length ∧ F.irreducible → g * g' * F.val ≠ g * g'
    }

/-
We show that our definition of graph action is consistent, that is, CG (G, X) is connected (acyclic) iff any resulting CG graph from our definition is connected (acyclic).
-/
example (g' : G') : (CayleyGraph X).Connected ↔ (group_action X g').Connected := by
  constructor
  · intro CG_connected
    intro g1 g2 g1_neq_g2
    have g1_neq_g2_prod : g1 * g' ≠ g2 * g' := by simp only [
        ne_eq, mul_left_inj,
        g1_neq_g2,
        not_false_eq_true
      ]
    exact CG_connected (g1 * g') (g2 * g') g1_neq_g2_prod
  intro g'CG_connected
  intro g1 g2 g1_neq_g2

  have g1_neq_g2_prod : g1 * g'⁻¹ ≠ g2 * g'⁻¹ := by simp only [
        ne_eq, mul_left_inj,
        g1_neq_g2,
        not_false_eq_true
      ]

  rcases g'CG_connected (g1 * g'⁻¹) (g2 * g'⁻¹) g1_neq_g2_prod with ⟨F, F_len, F_val⟩
  rw [mul_assoc g1 ↑g'⁻¹ g', mul_assoc g2 ↑g'⁻¹ g'] at F_val
  repeat rw [show ↑g'⁻¹ * ↑g' = (1 : G) by exact mul_left_inv _] at F_val
  rw [mul_one g1, mul_one g2] at F_val
  use F, F_len

example (g' : G') : (CayleyGraph X).Acyclic ↔ (group_action X g').Acyclic :=
  Iff.intro
  (λ CG_acyclic g F hF ↦ CG_acyclic (g * g') F hF)
  (
    by
      intro g'CG_acyclic g F ⟨F_len, F_irr⟩
      specialize g'CG_acyclic (g * g'⁻¹) F ⟨F_len, F_irr⟩
      rw [mul_assoc g ↑g'⁻¹ g'] at g'CG_acyclic
      repeat rw [show ↑g'⁻¹ * ↑g' = (1 : G) by exact mul_left_inv _] at g'CG_acyclic
      rwa [mul_one g] at g'CG_acyclic
  )

-------- Equivalence between properties of Cayley graph and groups --------

def CG := CayleyGraph X

theorem generative_connected_iff : generative_family X ↔ (CayleyGraph X).Connected := by
  constructor
  · intro h g1 g2 g1_neq_g2
    rcases h (g1⁻¹ * g2) with ⟨F, F_val⟩
    have cancel_prod : g1 * F.val = g2 := by rw[F_val, mul_inv_cancel_left]

    have F_length : 0 < F.length := by {
      by_contra h
      push_neg at h
      have F_eq_nil : F.elems = [] := List.length_eq_zero.mp (Nat.eq_zero_of_le_zero h)
      have F_val_eq_1 : F.val = 1 := by unfold Formula.val; rw [F_eq_nil]; rfl
      rw [F_val_eq_1] at cancel_prod
      rw [show g1 * 1 = g1 by exact LeftCancelMonoid.mul_one _] at cancel_prod
      exact g1_neq_g2 cancel_prod
    }
    exact ⟨F, ⟨F_length, cancel_prod⟩⟩

  intro h g
  by_cases hg : g = 1
  · let F : Formula G X := {
      elems := []
      elems_in_X := λ e e_in ↦ (List.not_mem_nil e).elim e_in
    }
    use F
    rw [
      show F.val = F.elems.prod by rfl,
      show F.elems = [] by rfl,
      hg, show [].prod = (1 : G) by rfl
    ]
  push_neg at hg
  rcases h 1 g hg.symm with ⟨F, _, F_val⟩
  use F
  rwa [←LeftCancelMonoid.one_mul F.val]

theorem free_acyclic_iff : free_family X ↔ (CayleyGraph X).Acyclic := by
  constructor
  · intro h
    by_contra h_acyclic
    rw [show (CayleyGraph X).Acyclic = ∀ g, ∀ (F : Formula G X), 0 < F.length ∧ F.irreducible → g * F.val ≠ g by rfl] at h_acyclic
    push_neg at h_acyclic
    rcases h_acyclic with ⟨g, F, ⟨F_len, F_irr⟩, F_val⟩
    have F_val_eq_1 := mul_right_eq_self.mp F_val
    exact (h F F_len F_irr) F_val_eq_1
  intro h
  intro F F_len F_irr
  by_contra F_val_eq_1
  specialize h 1 F ⟨F_len, F_irr⟩
  rw [F_val_eq_1, show (1 : G) * 1 = 1 by exact Units.instOneUnits.proof_1] at h
  contradiction

theorem tree_free_iff : is_free_group G ↔ (∃ (X : Set G), (CayleyGraph X).is_tree) := by
  constructor
  · intro ⟨X, X_gen, X_free⟩
    exact ⟨X, (generative_connected_iff X).mp X_gen, (free_acyclic_iff X).mp X_free⟩
  intro ⟨X, CG_connected, CG_acyclic⟩
  exact ⟨X, (generative_connected_iff X).mpr CG_connected, (free_acyclic_iff X).mpr CG_acyclic⟩
