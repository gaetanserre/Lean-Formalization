/-
 - Created in 2024 by Gaëtan Serré
-/

/-
- https://github.com/gaetanserre/Hirsch-Analysis
-/


import Mathlib.Init.Set
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Set Filter Topology Classical

set_option trace.Meta.Tactic.simp.rewrite true

set_option maxHeartbeats 1000000

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y)

----------------------------------COUNTABLE-----------------------------------

/--
A set E is countable if it exists a surjection from ℕ to E.
-/
def countable {u : Type} (E : Set u) := ∃ (f : ℕ → u), SurjOn f (univ) E

/--
ℕ is countable.
-/
lemma N_countable : countable (univ : Set ℕ) := by
  use (λ n ↦ n)
  intro n n_in
  use n

/--
ℤ is countable
-/
lemma Z_countable : countable (univ : Set ℤ) := by
  let f := λ (n : ℕ) ↦ if h : Even n then -((n / 2) : ℤ) else ((n - 1) / 2 + 1 : ℤ)
  have f_surj : SurjOn f univ univ := by {
    intro z _
    by_cases h : 0 < z
    · let n := 2 * (z - 1).toNat + 1
      have odd_n : Odd n := by use (z - 1).toNat
      use n
      refine ⟨trivial, ?_⟩
      rw [show f n = if h : Even n then -((n / 2) : ℤ) else ((n - 1) / 2 + 1 : ℤ) by rfl]
      split
      next h_if =>
        exfalso
        exact (Nat.odd_iff_not_even.mp odd_n) h_if
      have coe : (n : ℤ) = 2 * (z - 1) + 1 := by {
        have coe_tmp : ((z - 1).toNat : ℤ) = z - 1 := Int.toNat_of_nonneg (Int.le_sub_one_of_lt h)
        simpa [-Int.pred_toNat] using coe_tmp
      }
      rw [coe]
      calc (2 * (z - 1) + 1 - 1) / 2 + 1 = (2 * (z - 1)) / 2 + 1 := by simp
      _ = (z - 1) + 1 := by simp
      _ = z := by simp
    push_neg at h
    let n := 2 * (-z).toNat
    have even_n : Even n := by {
      unfold Even
      use (-z).toNat
      ring
    }
    use n
    refine ⟨trivial, ?_⟩
    rw [show f n = if h : Even n then -((n / 2) : ℤ) else ((n - 1) / 2 + 1 : ℤ) by rfl]
    split
    · have coe : ((-z).toNat : ℤ) = -z := Int.toNat_of_nonneg (Int.neg_nonneg_of_nonpos h)
      let m_z := - z
      calc - ((n : ℤ) / 2) = -(2 * ((-z).toNat : ℤ) / 2) := by rw [show (n : ℤ) = ((2 * m_z.toNat) : ℤ) by rfl]
      _ = -(2 * m_z / 2) := by rw [coe]
      _ = -(m_z) := by simp
      _ = - (-z) := rfl
      _ = z := by simp
    contradiction
  }

  use f

/--
Let E a set. E is countable iff it exists a surjection from a countable set A to E.
-/
lemma countable_trans {u : Type} {E : Set u} : countable E ↔ (∃ (v : Type), ∃ (A : Set v), (countable A ∧ ∃ (f : v → u), SurjOn f A E)) := by
  constructor
  · intro h_denomb
    use ℕ, univ
    constructor
    · exact N_countable
    rcases h_denomb with ⟨f, f_surj⟩
    use f
  intro h
  rcases h with ⟨v, A, ⟨g, g_surj⟩, f, f_surj⟩
  have comp_surj : SurjOn (f ∘ g) (univ) E := by {
    intro e e_in_E
    specialize f_surj e_in_E
    rcases f_surj with ⟨a, a_in_A, fa⟩
    specialize g_surj a_in_A
    rcases g_surj with ⟨n, n_in_N, gn⟩
    use n
    constructor
    · assumption

    unfold Function.comp
    rwa [gn]
  }
  use (f ∘ g)

/--
Let E be a countable set. Then any A ⊆ E is countable.
-/
lemma subset_of_countable_set {u : Type} {E : Set u} (A : Set u) (h : A ⊆ E) (he : countable E) : countable A := by
  let f := λ (e : u) ↦ e
  have f_surj : SurjOn f E A := by {
    intro a a_in_A
    use a, (h a_in_A)
  }
  exact countable_trans.mpr ⟨u, E, he, f, f_surj⟩

theorem prod_pow_primes_left {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
  (n m : ℕ) (neq : p ≠ q) : padicValNat p (p^n * q^m) = n := by
  rw [padicValNat.mul (NeZero.ne' (p^n)).symm (NeZero.ne' (q^m)).symm]
  have padic_p_qm_eq_0 : padicValNat p (q ^ m) = 0 := by
    rw [padicValNat.pow _ (Nat.Prime.ne_zero hq.elim), padicValNat_primes neq, mul_zero]
  rw [padicValNat.prime_pow, padic_p_qm_eq_0, add_zero]

theorem prod_pow_primes_right {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
  (n m : ℕ) (neq : q ≠ p) : padicValNat q (p^n * q^m) = m := by
  rw [padicValNat.mul (NeZero.ne' (p^n)).symm (NeZero.ne' (q^m)).symm]
  have padic_q_pn_eq_0 : padicValNat q (p ^ n) = 0 := by
    rw [padicValNat.pow _ (Nat.Prime.ne_zero hp.elim), padicValNat_primes neq, mul_zero]
  rw [padicValNat.prime_pow, padic_q_pn_eq_0, zero_add]

/--
ℕ² is countable.
-/
lemma N2_countable : countable (univ : Set (ℕ × ℕ)) := by
  let A := {n : ℕ | ∃ (a b : ℕ), n = 2^a * 3^b}
  let f := λ n ↦ if n ∈ A then (n.factorization 2, n.factorization 3) else (0, 0)
  have f_surj : SurjOn f A (univ : Set (ℕ × ℕ)) := by {
    intro x _
    let n := 2^x.1 * 3^x.2
    use n
    have n_in_A : n ∈ A := ⟨x.1, x.2, rfl⟩
    refine ⟨n_in_A, ?_⟩
    rw [show f n = if n ∈ A then (n.factorization 2, n.factorization 3) else (0, 0) by rfl]
    split
    · rw [show n.factorization 2 = padicValNat 2 n by rfl, show n.factorization 3 = padicValNat 3 n by rfl]
      rw [prod_pow_primes_left x.1 x.2 (show 2 ≠ 3 by simp), prod_pow_primes_right x.1 x.2 (show 3 ≠ 2 by simp)]
    contradiction
  }

  exact countable_trans.mpr ⟨ℕ, A, subset_of_countable_set A (λ _ _ ↦ trivial) (N_countable), f, f_surj⟩

/--
We use a different definition of a set being countable to match the book as much as possible. For completeness, we show that our definition is equivalent to Mathlib's. It corresponds to Corollary 1.5.
-/
lemma countable_iff {u : Type} {E : Set u} [∀ (e : u), Decidable (e ∈ E)] (hE : Set.Nonempty E) : countable E ↔ Set.Countable E := by
  let s_t := {e : u // e ∈ E}
  constructor
  · intro h
    rcases h with ⟨f, f_surj⟩
    have surj' : ∀ e ∈ E, ∃ n, f n = e := by {
      intro e e_in_E
      specialize f_surj e_in_E
      rcases f_surj with ⟨n, _, f_n⟩
      use n
    }

    let g := λ (e : s_t) ↦ Nat.find (surj' e.val e.property)

    have g_inj : Function.Injective g := by {
      have f_g_id : ∀e (h : e ∈ E), f (g ⟨e, h⟩) = e := by {
        intro e he
        have h_g_e : g ⟨e, he⟩ = Nat.find (surj' e he) := by rfl
        have tmp := Nat.find_spec (surj' e he)
        rwa [←h_g_e] at tmp
      }
      intro e1 e2 hg
      ext
      rw [←f_g_id e1.val e1.property, ←f_g_id e2.val e2.property, hg]
    }

    use g

  intro h
  rcases h with ⟨f, f_inj⟩
  let fE := {n : ℕ | ∃ (e : s_t), f e = n}
  have fE_countable : countable fE := subset_of_countable_set fE (λ _ _ ↦ trivial) N_countable

  have fE_dual_non_empty : ∀ n ∈ fE, Set.Nonempty {e | f e = n} := by {
    intro n hn
    rcases hn with ⟨e, fe_n⟩
    use e, fe_n
  }

  let ϕ := λ n h ↦ (Set.Nonempty.some (fE_dual_non_empty n h))
  let f' := λ (n : ℕ) ↦ if h : n ∈ fE then (ϕ n h).val else (Set.Nonempty.some (hE))

  have f'_surj : SurjOn f' fE E := by {
    intro e e_in_E
    let e' : s_t := ⟨e, e_in_E⟩
    use (f e')
    have fe'_in_fE : f e' ∈ fE := by use e'
    refine ⟨fe'_in_fE, ?_⟩
    rw [show f' (f e') = if h : (f e') ∈ fE then (ϕ (f e') h).val else (Set.Nonempty.some (hE)) by rfl]
    split
    ·
      have ff'e'_eq_fe' : f (ϕ (f e') fe'_in_fE) = (f e') :=
        Set.Nonempty.some_mem (fE_dual_non_empty (f e') fe'_in_fE)
      specialize f_inj ff'e'_eq_fe'
      have eq_subtype : ∀ {e1 e2 : s_t}, e1 = e2 → e1.val = e2.val :=
        λ {_} {_} a ↦ congrArg Subtype.val a
      apply (eq_subtype f_inj)
    contradiction
  }

  exact countable_trans.mpr ⟨ℕ, fE, fE_countable, f', f'_surj⟩

/--
The product of two countable sets is countable. (Proposition 1.6 p.2)
-/
lemma product_countable_set {u v : Type} {E : Set u} {A : Set v} (he : countable E) (ha : countable A) : countable {x : u × v | x.1 ∈ E ∧ x.2 ∈ A} := by
  rcases he with ⟨fe, fe_surj⟩
  rcases ha with ⟨fa, fa_surj⟩
  let ϕ := λ (x : ℕ × ℕ) ↦ (fe x.1, fa x.2)
  have ϕ_surj : SurjOn ϕ univ {x : u × v | x.1 ∈ E ∧ x.2 ∈ A} := by {
    intro x ⟨hx1, hx2⟩
    rcases fe_surj hx1 with ⟨e, _, hfe⟩
    rcases fa_surj hx2 with ⟨a, _, hfa⟩
    use (e, a)
    refine ⟨trivial, ?_⟩
    rw [show ϕ (e, a) = (fe e, fa a) by rfl, hfe, hfa]
  }
  exact countable_trans.mpr ⟨ℕ×ℕ, univ, N2_countable, ϕ, ϕ_surj⟩

/--
ℚ is countable. (Example 1 p.3)
-/
lemma Q_countable : countable (univ : Set ℚ) := by
  let A := {x : ℤ × ℕ | 0 < x.2 ∧ x.1.natAbs.Coprime x.2}

  let f := λ (x : ℤ × ℕ) ↦ if h : x ∈ A then ({num:=x.1, den:=x.2, den_nz:=Nat.not_eq_zero_of_lt h.1, reduced:=h.2} : ℚ) else 0

  have f_surj : SurjOn f A univ := by {
    intro q _
    let x := (q.num, q.den)
    use x
    refine ⟨⟨Rat.den_pos q, q.reduced⟩, ?_⟩
    rw [show f x = if h : x ∈ A then ({num:=x.1, den:=x.2, den_nz:=Nat.not_eq_zero_of_lt h.1, reduced:=h.2} : ℚ) else 0 by rfl]
    split
    · rfl
    next h_if =>
      exfalso
      exact h_if ⟨Rat.den_pos q, q.reduced⟩
  }

  have countable_prod : countable (univ : Set (ℤ × ℕ)) := by {
    have eq_set : {(x : ℤ × ℕ) | x.1 ∈ univ ∧ x.2 ∈ univ} = (univ : Set (ℤ × ℕ)) := by {
      ext x
      constructor
      · intro _
        trivial
      intro _
      exact ⟨trivial, trivial⟩
    }
    have univ_countable := product_countable_set Z_countable N_countable
    rwa [eq_set] at univ_countable
  }


  have countable_A := subset_of_countable_set A (show A ⊆ univ by exact λ _ _ ↦ trivial) countable_prod

  exact countable_trans.mpr ⟨ℤ×ℕ, A, countable_A, f, f_surj⟩

/--
Let A and E two sets such that E is uncountable. If it exists a surjection from A to E, then A is uncountable.
-/
lemma uncountable_trans {u v : Type} (A : Set u) {E : Set v} (h : ¬countable E) : (∃ (f : u → v), SurjOn f A E) → ¬countable A := by
  intro exists_surj
  rcases exists_surj with ⟨f, f_surj⟩
  by_contra h_countable; push_neg at h_countable
  rcases h_countable with ⟨g, g_surj⟩
  have fg_surj_N_E : SurjOn (f ∘ g) univ E := by {
    intro e e_in_E
    rcases f_surj e_in_E with ⟨a, a_in_A, fa⟩
    rcases g_surj a_in_A with ⟨n, n_in_N, gn⟩
    use n, n_in_N
    rwa [show (f ∘ g) n = f (g n) by rfl, gn]
  }
  have E_countable : countable E := by use (f ∘ g)
  exact h E_countable

/--
Corrolary: if A ⊆ E is uncountable, then E is uncountable.
-/
lemma subset_of_uncountable_set {u : Type} {E A : Set u} (h : A ⊆ E) (uncountable : ¬ countable A) : ¬ countable E := by
  by_contra h_contr
  let f := λ (e : u) ↦ e
  have f_surj : SurjOn f E A := λ e e_in_A ↦ ⟨e, h e_in_A, rfl⟩
  exact uncountable.elim (countable_trans.mpr ⟨u, E, h_contr, f, f_surj⟩)


------------------------------FORMALIZATION-----------------------------------

/--
For any real number x and any positive number ε, it exists a rational q such that |x - q| < ε.
-/
lemma Q_dense (x : ℝ) : ∀ ε > 0, ∃ (q : ℚ), |x - q| < ε :=
by
  intro ε ε_pos
  have h : x < x + ε := by linarith
  obtain ⟨q, hql, hqr⟩ := exists_rat_btwn h
  use q
  have x_minus_q_neg : x - q < 0 := by linarith
  have abs_eq_neg : |x - q| = -(x - q) := by {
    rw [abs_eq_neg_self]
    linarith
  }
  rw [abs_eq_neg, show -(x - q) = q - x by ring]
  linarith

/--
For any real number x, it exists a sequence of rational that tends to x.
-/
example (x : ℝ) : ∃ (u : ℕ → ℚ), Tendsto (λ n ↦ ((u n) : ℝ)) atTop (𝓝 x) :=
by
  let A := λ (n : ℕ) ↦ {q : ℚ | |x - q| < (1 / (n+1))}
  have non_empty : ∀ n,  Set.Nonempty (A n) := by {
    intro n
    obtain ⟨q, hq⟩ : ∃ (q : ℚ), |x - q| < (1 / (n+1)) := Q_dense x (1 / (n+1)) (Nat.one_div_pos_of_nat)
    use q, hq
  }

  let u := λ (n : ℕ) ↦ Set.Nonempty.some (non_empty n)
  use u
  rw [Metric.tendsto_atTop']
  have dst : ∀ n, dist ((u n) : ℝ) x = |x - ((u n) : ℝ)| := λ _ ↦ Metric.mem_sphere'.mp rfl
  simp_rw [dst]
  intro ε ε_pos
  obtain ⟨N, hn⟩ : ∃ (N : ℕ), 1 / (N + 1) < ε := by {
    use (⌈1 / ε⌉₊)
    have R_pos: 0 < (⌈1 / ε⌉₊ + 1 : ℝ) := Nat.cast_add_one_pos ⌈1 / ε⌉₊
    rw [show 1 / (⌈1 / ε⌉₊ + 1 : ℝ) = (⌈1 / ε⌉₊ + 1 : ℝ)⁻¹ by exact one_div (⌈1 / ε⌉₊ + 1 : ℝ)]
    rw [inv_lt R_pos ε_pos, show ε⁻¹ = 1 / ε by exact inv_eq_one_div ε]
    calc 1 / ε <= (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil (1 / ε)
    _ < (⌈1 / ε⌉₊ + 1 : ℝ) := lt_add_one (⌈1 / ε⌉₊ : ℝ)
  }
  use N
  intro n N_ltn
  calc |x - ((u n) : ℝ)| < 1 / (n + 1 : ℝ) := Nonempty.some_mem (non_empty n)
  _ < 1 / (N + 1 : ℝ) := Nat.one_div_lt_one_div N_ltn
  _ < ε := hn

/--
The power set of ℕ is uncountable. (Example 4 p.3)
-/
lemma powerset_N_uncountable : ¬countable (𝒫 (univ : Set ℕ)) :=
by

  by_contra h

  rcases h with ⟨ϕ, h⟩

  let A := {n : ℕ | n ∉ ϕ n}

  specialize h (λ _ _ ↦ trivial : A ∈ 𝒫 (univ : Set ℕ))
  rcases h with ⟨a, _, ha⟩

  by_cases ain : a ∉ A
  · have a_in_phi : ¬ (a ∉ ϕ a) := ain
    push_neg at a_in_phi
    rw [ha] at a_in_phi
    exact ain a_in_phi

  push_neg at ain
  have a_notin_phi_a : a ∉ ϕ a := ain
  rw [ha] at a_notin_phi_a
  exact a_notin_phi_a ain

/-
- The set of all sequences in {0, 1}
-/
def zero_one := {u: ℕ → ℕ | ∀n, u n = 0 ∨ u n = 1}

/--
The set of all sequences in {0, 1} is uncountable. (Example 5 p.3)
-/
lemma zero_one_uncountable : ¬countable zero_one :=
by
  let f := λ (ϕ : ℕ → ℕ) ↦ {n : ℕ | ϕ n = 1}

  have f_surj : SurjOn f zero_one (𝒫 (univ : Set ℕ)) := by {
    intro A _
    let ϕ := indicator A (λ _ ↦ 1)
    use ϕ
    have ϕ_in_zero_one : ϕ ∈ zero_one := by {
      intro n
      by_cases h : n ∈ A
      · have ind_eq_1 : ϕ n = 1 := by {
          rw [indicator_apply_eq_self]
          exact λ a ↦ (a h).elim
        }
        apply Or.inr; assumption

      have ind_eq_0 : ϕ n = 0 := by {
          rw [indicator_apply_eq_zero]
          exact λ a ↦ (h a).elim
      }
      apply Or.inl; assumption
    }
    refine ⟨ϕ_in_zero_one, ?_⟩
    ext n
    constructor
    · intro n_in_f_ϕ
      have ϕn_eq_1 : ϕ n = 1 := n_in_f_ϕ
      rw [indicator_apply_eq_self] at ϕn_eq_1
      by_contra n_notin_A
      specialize ϕn_eq_1 n_notin_A
      contradiction

    intro n_in_A
    have ϕ_eq_1 : ϕ n = 1 := by {
      rw [indicator_apply_eq_self]
      intro n_notin_A
      exact (n_notin_A n_in_A).elim
    }
    exact ϕ_eq_1
  }
  exact uncountable_trans zero_one powerset_N_uncountable ⟨f, f_surj⟩

example : ¬ countable (univ : Set (ℕ → ℕ)) :=
  subset_of_uncountable_set (λ _ _ ↦ trivial) zero_one_uncountable

/--
Let A be a family of disjoint, non-empty, open sets of ℝ. Then A is countable. (Example 9 p.4)
-/
example (A : NNReal → Set ℝ) (h_nonempty : ∀ t, Set.Nonempty (A t)) (h_open : ∀ t, IsOpen (A t)) (h_disjoint : ∀ t1 t2, t1 ≠ t2 → Disjoint (A t1) (A t2)) : countable {A t | t : NNReal} :=
by

  let q_A_t := λ t ↦ {q : ℚ | (q : ℝ) ∈ A t}
  have nonempty_q_A_t : ∀ t, Set.Nonempty (q_A_t t) := by {
    intro t
    rcases (h_nonempty t) with ⟨x, hx⟩
    specialize h_open t
    rw [Metric.isOpen_iff] at (h_open)
    rcases h_open x hx with ⟨ε, hε, ball_in_At⟩
    obtain ⟨q, hql, hqr⟩ := exists_rat_btwn (show x < x + ε by linarith)
    have q_dist : q - x < ε := by linarith
    have pos_abs : q - x = |q - x| := (abs_of_pos (show 0 < q - x by linarith)).symm
    rw [pos_abs, show |q - x| = dist (q : ℝ) x by rfl, ←Metric.mem_ball] at q_dist
    use q, (ball_in_At q_dist)
  }

  let q_A := λ (q : ℚ) ↦ {x | ∃ t, A t = x ∧ (q : ℝ) ∈ A t}
  have nonempty_q_A : ∀ q, (∃ t, q ∈ (q_A_t t)) → Set.Nonempty (q_A q) := by {
    intro q h
    rcases h with ⟨t, hq⟩
    use (A t), t
    refine ⟨rfl, ?_⟩
    use hq
  }

  let ϕ := λ q hq ↦ Set.Nonempty.some (nonempty_q_A q hq)
  let f := λ (q : ℚ) ↦ if h : ∃ t, q ∈ (q_A_t t) then ϕ q h else A 0

  have f_surj : SurjOn f univ {A t | t : NNReal} := by {
    intro At ⟨t, h⟩
    rw [←h]
    rcases nonempty_q_A_t t with ⟨q, hq⟩
    use q
    refine ⟨trivial, ?_⟩
    rw [show f q = if h : ∃ t, q ∈ (q_A_t t) then ϕ q h else A 0 by rfl]
    split
    next h_if =>
      · have rfl_ϕ : ϕ q h_if ∈ q_A q := Nonempty.some_mem (nonempty_q_A q h_if)
        rcases rfl_ϕ with ⟨t2, h_eq_t2, hq2⟩
        rw [←h_eq_t2]

        have At_eq_At2 : A t = A t2 := by {
          by_contra h_neg; push_neg at h_neg
          have t_neq : t ≠ t2 := λ a ↦ h_neg (congrArg A a)
          have disjoint : Disjoint (A t) (A t2) := h_disjoint t t2 t_neq
          have q_not_in : (q : ℝ) ∉ A t2 := disjoint_left.mp disjoint hq
          exact q_not_in hq2
        }
        rw [At_eq_At2]

    next h_if =>
      push_neg at h_if
      specialize h_if t
      contradiction
  }

  exact countable_trans.mpr ⟨ℚ, univ, Q_countable, f, f_surj⟩
