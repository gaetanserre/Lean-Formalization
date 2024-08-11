/-
  Created in 2024 by Gaëtan Serré
-/


import Mathlib.Order.WellFoundedSet

set_option maxHeartbeats 1000000

open Set

variable {α β : Type*} {A : Set α}

def injA {A B : Set α} (a : A) : (A ∪ B).Elem := ⟨a.1, mem_union_left B a.2⟩
def injB {A B : Set α} (b : B) : (A ∪ B).Elem := ⟨b.1, mem_union_right A b.2⟩

lemma no_inj_imp_group_union_right {B : Set α} [Group (A ∪ B).Elem]
    (no_inj : ∀ (f : B → A), ¬f.Injective) :
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
  suffices f.Injective by specialize no_inj f; contradiction
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

variable (B : Set α) [LT B] (hB : WellFounded (fun (a b : B) ↦ a < b))
    (no_inj : ∀ (f : B → A), ¬ f.Injective)

def AB [Group (A ∪ B).Elem] (a : A) :=
  {b : B | ((injA a) * (injB b)).1 ∈ B}

def S [Group (A ∪ B).Elem] (a : A) :=
  {p : (B × B) | p.1 ∈ (AB B a) ∧ ((injA a) * (injB p.1)).1 = p.2.val}

instance : LT (B × B) where
  lt := Prod.Lex (· < ·) (· < ·)

lemma S_WF [Group (A ∪ B).Elem] (a : A) : (S B a).IsWF := by
  have univ_wf : univ.IsWF := WellFounded.onFun (WellFounded.prod_lex hB hB)
  exact IsWF.mono univ_wf (fun _ _ => trivial)

lemma S_ne [Group (A ∪ B).Elem] (a : A) : (S B a).Nonempty := by
  obtain ⟨b, hb⟩ := no_inj_imp_group_union_right no_inj a
  let c : B := ⟨(injA a * injB b).1, hb⟩
  exact ⟨⟨b, c⟩, hb, rfl⟩

noncomputable def f [Group (A ∪ B).Elem] :=
  fun (a : A) ↦
    (WellFounded.min (S_WF B hB a) univ (nonempty_iff_univ_nonempty.1 (S_ne B no_inj a).to_subtype)).1

/--
  **Main theorem**: Let `A` be any set. If there exists a set `B` such that the `<` relation over
  `B` is well-founded and that it exists a group structure on `A ∪ B`, then it exists a
  well-ordered `<` relation over `A`, i.e., it implies the *Well-ordering theorem*.
-/
theorem A_is_WF [Group (A ∪ B).Elem] : WellFounded (fun a b ↦ f B hB no_inj a < f B hB no_inj b) :=
  @WellFounded.onFun A (B × B) (fun (a b : B × B) ↦ a < b) (f B hB no_inj)
    (WellFounded.prod_lex hB hB)
