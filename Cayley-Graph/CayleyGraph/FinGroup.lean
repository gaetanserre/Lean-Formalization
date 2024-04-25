/-
 - Created in 2024 by Gaëtan Serré
 -/

import Mathlib
open Classical

set_option maxHeartbeats 600000

class FinGroup (G : Type*) [Fintype G] extends Group G

structure Formula (G : Type*) [Fintype G] [FinGroup G] (X : Set G) where
  elems : List G
  elems_in_X : ∀ e ∈ elems, e ∈ X ∨ e⁻¹ ∈ X


namespace Formula
variable {G : Type*} [Fintype G] [FinGroup G] {X : Set G} (F : Formula G X)
def val := F.elems.prod
def length := F.elems.length
def get (i : Fin (F.length)) := F.elems.get i
def irreducible :=
  if h : 1 < F.length then
    ∀ (i : Fin F.length), (F.get i) * (F.get (i + {val:=1, isLt:=h})) ≠ 1
  else if h : F.length = 1 then F.get {val:=0, isLt:=by rw[h]; exact Nat.zero_lt_one} ≠ 1
  else F.elems = []
end Formula

variable {G : Type*} [Fintype G] [FinGroup G] [Inhabited G]

def generative_family (X : Set G) := ∀ (g : G), ∃ (F : Formula G X), F.val = g

def free_family (X : Set G) := ∀ (F : Formula G X), (h : 0 < F.length) → F.irreducible → F.val ≠ 1

def is_free_group (G : Type*) [Fintype G] [FinGroup G] [Inhabited G] := ∃ (X : Set G), generative_family X ∧ free_family X


/- lemma empty_formula_irreducible {F : Formula G X} (hF : F.elems = []) : F.irreducible := by
  have Fl : F.length = 0 := List.length_eq_zero.mpr hF
  unfold Formula.irreducible
  split
  · linarith
  split
  · linarith
  assumption

lemma single_formula_irreducible {F : Formula G X} (hF : ∃ g, g ≠ 1 ∧ F.elems = [g]) : F.irreducible := by
  rcases hF with ⟨g, g_neq_id, F_elem⟩

  have Fl : F.length = 1 := by unfold Formula.length; rw [F_elem]; rfl
  unfold Formula.irreducible
  split
  · linarith
  have F_get_eq_g : F.get {val:=0, isLt:=by rw[Fl]; exact Nat.zero_lt_one} = g := by {
    unfold Formula.get
    let i : Fin F.length := {val:=0, isLt:=by rw[Fl]; exact Nat.zero_lt_one}
    have isLt : ↑i < F.elems.length := by
      unfold Formula.length at Fl
      rw [Fl]
      exact zero_lt_one
    rw [←List.getI_eq_get F.elems isLt, congrFun (congrArg List.getI F_elem) i.val]
    rw [show ↑i = 0 by rfl]
    rfl
  }
  rwa [F_get_eq_g]

theorem toIrreducible (F : Formula G X) : ∃ (F' : Formula G X), F'.irreducible ∧ F'.val = F.val := by
  --by_contra h; push_neg at h
  by_cases hFl_0 : F.length = 0
  · have F_empty : F.elems = [] := (List.length_eq_zero.mp) hFl_0
    exact ⟨F, empty_formula_irreducible F_empty, rfl⟩
  by_cases hFl : F.length = 1
  · obtain ⟨g, F_elems⟩ := List.length_eq_one.mp hFl
    by_cases hg : g = 1
    · let F' : Formula G X := {elems := [], elems_in_X:=λ _ _ ↦ by contradiction}
      have Fval : F.val = 1 := by unfold Formula.val; rw [F_elems, hg]; exact List.prod_singleton
      have F'val : F'.val = 1 := by unfold Formula.val; rw [show F'.elems = [] by rfl]; rfl
      refine ⟨F', empty_formula_irreducible (show F'.elems = [] by rfl), ?_⟩
      rw [Fval, F'val]
    push_neg at hg
    exact ⟨F, single_formula_irreducible ⟨g, hg, F_elems⟩, rfl⟩
  push_neg at hFl
  have lt_one : 1 < F.length := by
    have lt_zero := Nat.zero_lt_of_ne_zero hFl_0
    exact Nat.lt_of_le_of_ne lt_zero (id (Ne.symm hFl))

  sorry

/- Fonction recursive qui casse une liste en pairs. Preuve par induction sur les listes. -/

def irre (l : List ℤ) :=
  let rec aux (l : List ℤ) (acc : List ℤ) :=
    match l with
    | [] => acc
    | hd::[] => if hd = 0 then acc else acc.concat hd
    | hd1::hd2::tl =>
      if hd1 + hd2 = 0 then aux tl acc
      else if hd1 = 0 then aux (hd2::tl) acc
      else if hd2 = 0 then aux (hd1::tl) acc
      else aux (hd2::tl) (acc.concat hd1)
  aux l []


example (l : List ℤ) (z : ℤ) (h : irre l = l) : irre (l.tail) = l.tail := by
  induction l with
  | nil => sorry
  | cons hd tl h2 =>
    rw [show (hd :: tl).tail = tl by rfl]

    sorry

example (l : List ℤ) :
  if h : 1 < (irre l).length then ∀ (i : Fin (irre l).length), ((irre l).get i) * ((irre l).get (i + {val:=1, isLt:=h})) ≠ 1
  else if h : (irre l).length = 1 then (irre l).get {val:=0, isLt:=by rw[h]; exact Nat.zero_lt_one} ≠ 1
  else l = [] := by
  induction l with
  | nil =>
    split
    · contradiction
    next h =>
      push_neg at h
      split
      · contradiction
      rfl
  | cons hd tl h =>
    let l' := hd::tl
    split at h
    next h_length =>
      sorry
    split at h
    next h_length =>
      split
      · next h_contra =>
        sorry
      sorry

    --rw [show hd::tl = l' by rfl]
    sorry

/- def irre (l : List ℤ) :=
  let f (acc : List ℤ × ℤ) (z : ℤ) := if acc.2 + z = 0 then (acc.1, z) else (acc.1.concat acc.2, z)
  if h : l ≠ [] then
    let acc := (l.tail.foldl f ([], l.head h))
    if l.get {val:=l.length - 1, isLt:=by sorry} + acc.2 = 0 then acc.1
    else acc.1.concat acc.2
  else [] -/

#eval irre [1, 2, -1, -3, 3] -/
