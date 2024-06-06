import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Kernel.Disintegration.Basic
open MeasureTheory Set ProbabilityTheory
/--
  If two constant functions are equal a.e w.r.t. a measure that is positive when applied to univ,
  then the two constants are equal.
-/
lemma constant_ae_eq_imp_eq {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    (hμ : μ univ ≠ 0) (c d : β) (h_ae : (fun (_: α) ↦ c) =ᵐ[μ] (fun (_: α) ↦ d)) :
    c = d := by
  by_contra h
  push_neg at h
  have : μ ({(_ : α) | c = d} ∪ {(_ : α) | c = d}ᶜ) = 0 := by
    have : μ {(_ : α) | c = d} = 0 := by
      have : {(_ : α) | c = d} = ∅ := by exact subset_eq_empty (fun _ ↦ h) rfl
      rw [this]
      exact OuterMeasureClass.measure_empty μ
    exact measure_union_null this h_ae
  rw [← union_compl_self {(_ : α) | c = d}] at hμ
  contradiction

/-
  Law of total probability using `condKernel`.
-/
namespace ProbTotalLaw

variable {Ω α: Type} [Nonempty Ω] [MeasurableSpace Ω] [MeasurableSpace α] [StandardBorelSpace Ω]

/- instance {μ : Measure α} {ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    IsFiniteMeasure (μ.prod ν) where
  measure_univ_lt_top := by
    rw [μ.prod_apply MeasurableSet.univ]
    simp_rw [preimage_univ, lintegral_const]
    suffices ν univ * μ univ < ⊤ * ⊤ by exact this
    exact ENNReal.mul_lt_mul
      (IsFiniteMeasure.measure_univ_lt_top) (IsFiniteMeasure.measure_univ_lt_top) -/

variable (μ : Measure α) (ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem probability_total_law :
    ∀ s, μ s = ∫⁻ x in s, ∫⁻ _, 1 ∂(μ.prod ν).condKernel x ∂μ := by
  intro s
  simp_rw [fun _ ↦ lintegral_one]
  have is_prob_measure : ∀ x, (μ.prod ν).condKernel x univ = 1 :=
    fun x ↦ isProbabilityMeasure_iff.mp (IsMarkovKernel.isProbabilityMeasure x)
  simp_rw [is_prob_measure]
  exact (set_lintegral_one s).symm

variable [IsProbabilityMeasure ν]

lemma apply_fst : (μ.prod ν).fst = μ := by
  rw [show (μ.prod ν).fst = (μ.prod ν).map Prod.fst by rfl]
  rw [Measure.map_fst_prod, measure_univ, one_smul]

lemma apply_comp : μ.prod ν = μ ⊗ₘ (μ.prod ν).condKernel := by
  rw (config := {occs := .pos [2]}) [← apply_fst μ ν]
  exact (Measure.compProd_fst_condKernel (μ.prod ν)).symm

end ProbTotalLaw

/-
 Tower property of conditional expectation using `condexp`.
-/
namespace ExpCond

variable {Ω F : Type*}
[NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
{m2 m₁ mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → F}

/- example (hm₁ : m₁ ≤ mΩ) (m₂ : m2 ≤ m₁) [SigmaFinite (μ.trim hm₁)] :
    ∀ (s : Set Ω), MeasurableSet[m2] s → ∫ x in s, condexp m2 μ X x ∂μ
    = ∫ x in s, condexp m₁ μ (condexp m2 μ X) x ∂μ := by
  intro s hs
  exact (setIntegral_condexp hm₁ (integrable_condexp) (m₂ s hs)).symm -/

theorem tower_property {X : Ω → F} (hX : Integrable X μ) (hm₁ : m₁ ≤ mΩ) (m₂ : m2 ≤ m₁) [SigmaFinite (μ.trim (m₂.trans hm₁))] :
    μ[X | m2] =ᵐ[μ] μ[μ[X | m₁] | m2] := by
  have : SigmaFinite (μ.trim hm₁) := sigmaFiniteTrim_mono hm₁ m₂
  apply ae_eq_condexp_of_forall_setIntegral_eq
  · exact integrable_condexp
  · intro s _ _
    exact integrable_condexp.integrableOn
  · intro s hs _
    rw [setIntegral_condexp (m₂.trans hm₁) hX hs]
    have hs2 : MeasurableSet[m₁] s := m₂ s hs
    rw [setIntegral_condexp hm₁ hX hs2]
  exact StronglyMeasurable.aeStronglyMeasurable' (stronglyMeasurable_condexp)

end ExpCond

/-
  Law of total expectation using `condExp`.
-/
namespace ExpTotal

variable {Ω F : Type*}
[NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
{m2 m₁ mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → F}

open ExpCond

def S : Set (Set Ω) := {∅, univ}

lemma destruct_S : ∀ ⦃t : Set Ω⦄, t ∈ S → t = ∅ ∨ t = univ := fun _ ht ↦ ht

lemma S_apply : (∅ : Set Ω) ∈ S ∧ (univ : Set Ω) ∈ S :=
  ⟨mem_insert ∅ {univ}, mem_insert_of_mem ∅ rfl⟩

/--
  The trivial σ-algebra : {∅, univ}.
-/
def m_trivial : MeasurableSpace Ω := MeasurableSpace.generateFrom S

/--
  The trivial σ-algebra is less or equal then any σ-algebra.
-/
lemma m_trivial_le : ∀ (m : MeasurableSpace Ω), m_trivial ≤ m := by
  intro _
  apply MeasurableSpace.generateFrom_le
  intro _ ht
  cases destruct_S ht with
  | inl h =>
    rw [h]
    exact MeasurableSet.empty
  | inr h =>
    rw [h]
    exact MeasurableSet.univ

/--
  The trivial σ-algebra is only composed of ∅ and univ.
-/
lemma measurableSet_S {s : Set Ω} : MeasurableSet[m_trivial] s → s ∈ S := by
  apply MeasurableSpace.generateFrom_induction
  · simp only [imp_self, implies_true]
  · exact S_apply.1
  intro t ht
  cases destruct_S ht with
  | inl ht =>
    rw [ht]
    have : ∅ᶜ = (univ : Set Ω) := compl_empty
    rw [compl_empty]
    exact S_apply.2
  | inr ht =>
    rw [ht, compl_univ]
    exact S_apply.1
  intro f hf
  by_cases h : ∃ n, f n = univ
  · have : ⋃ i, f i = univ := by
      apply iUnion_eq_univ_iff.mpr
      intro x
      rcases h with ⟨n, h⟩
      use n
      rw [h]
      trivial
    rw [this]
    exact S_apply.2
  push_neg at h
  have : ⋃ i, f i = ∅ := by
    have : ∀ n, f n = ∅ := by
      intro n
      specialize h n
      cases destruct_S (hf n) with
      | inr _ => contradiction
      | inl _ => assumption
    exact iUnion_eq_empty.mpr this
  rw [this]
  exact S_apply.1

variable [IsProbabilityMeasure μ]

/--
  The trivial σ-algebra and any other σ-algebra are independent.
-/
lemma m_trivial_indep (m₁ : MeasurableSpace Ω) : Indep m₁ m_trivial μ := by
  apply (Indep_iff m₁ m_trivial μ).mpr
  intro t1 t2 _ ht2
  cases destruct_S (measurableSet_S ht2) with
  | inl h =>
    have : t1 ∩ t2 = ∅ := by
      rw [h]
      exact inter_empty t1
    rw [this, h, OuterMeasureClass.measure_empty μ, mul_zero]
  | inr h =>
    have : t1 ∩ t2 = t1 := by
      rw [h]
      exact inter_univ t1
    rw [this, h, measure_univ, mul_one]

/--
  The expectation conditioned to the trivial σ-algebra is equal a.e. to the expectation.
-/
lemma condition_m_trivial [IsProbabilityMeasure μ] {X : Ω → F} (hm₁ : m₁ ≤ mΩ)
    (hf : StronglyMeasurable[m₁] X) [SigmaFinite (μ.trim (m_trivial_le mΩ))] :
    μ [X | m_trivial] =ᵐ[μ] (fun _ ↦ μ[X]) :=
  condexp_indep_eq hm₁ (m_trivial_le mΩ) hf (m_trivial_indep m₁)

/--
  The law of total expectation.
-/
theorem total_expectation_law [IsProbabilityMeasure μ] {X : Ω → F} (hX : Integrable X μ)
    (hm₁ : m₁ ≤ mΩ) [SigmaFinite (μ.trim hm₁)] (hm : StronglyMeasurable[m₁] X) :
     μ[μ[X | m₁]] = μ[X] := by
  have μ_univ_neq_0 : μ univ ≠ 0 := (NeZero.ne' (μ univ)).symm
  apply constant_ae_eq_imp_eq μ_univ_neq_0
  have tower : μ[X|m_trivial] =ᵐ[μ] μ[μ[X|m₁]|m_trivial] := tower_property hX hm₁ (m_trivial_le m₁)
  have sMeasurable : StronglyMeasurable[m₁] (μ[X | m₁]) := stronglyMeasurable_condexp
  filter_upwards [condition_m_trivial hm₁ sMeasurable, condition_m_trivial hm₁ hm, tower]
    with a ha1 ha2 ha3
  rw [← ha1, ← ha3, ha2]

end ExpTotal

namespace MeasureTheory

variable {Ω F : Type*} [mΩ : MeasurableSpace Ω]
    [MeasurableSpace F] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F]

/--
  The σ-algebra generated by a r.v.
-/
def gen_sigma (Y : Ω → F) := MeasurableSpace.generateFrom {S | ∃ (A : Set F), MeasurableSet A ∧ Y⁻¹' A = S}

/--
  The σ-algebra generated by a r.v is less or equal than the encompassing σ-algebra.
-/
lemma sigma_generated_le {Y : Ω → F} (hY : Measurable Y) :
    gen_sigma Y ≤ mΩ := by
  apply MeasurableSpace.generateFrom_le
  intro t ht
  rcases ht with ⟨A, hA, ht⟩
  rw [← ht]
  exact hY hA

/--
  The condition probability.
-/
noncomputable def Measure.condProb (μ : Measure Ω) (A : Set Ω) (Y : Ω → F) :=
  μ[A.indicator (fun (_ : Ω) ↦ (1 : ℝ)) | gen_sigma Y]

end MeasureTheory

namespace TotalProba

open ENNReal

variable {Ω F : Type*}
[NormedAddCommGroup F] [NormedSpace ℝ F]
[CompleteSpace F] [MeasurableSpace F]
{m2 m₁ mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → F} (hY : Measurable Y)

/--
  The law of total probability using the law of total expectation.
-/
theorem total_probability_law [IsProbabilityMeasure μ] {A : Set Ω} (hA : MeasurableSet[gen_sigma Y] A)
    [SigmaFinite (μ.trim (sigma_generated_le hY))] :
    (μ A).toReal = μ[μ.condProb A Y] := by


  have hAmΩ : MeasurableSet A := by exact (sigma_generated_le hY) A hA

  have hAE : StronglyMeasurable[gen_sigma Y] (A.indicator (fun (_ : Ω) ↦ (1 : ℝ))) := by
    exact StronglyMeasurable.indicator stronglyMeasurable_const hA

  have : ∫ a, A.indicator (fun x ↦ 1) a ∂μ = (μ A).toReal := by
    rw [integral_indicator hAmΩ]
    have t : 0 ≤ᵐ[μ.restrict A] (fun _ ↦ (1 : ℝ)) := by
      suffices 0 ≤ (fun (_ : Ω) ↦ (1 : ℝ)) by sorry
      intro x
      simp only [Pi.zero_apply, zero_le_one]

    have tt : AEStronglyMeasurable (fun _ ↦ (1 : ℝ)) (μ.restrict A) := by sorry

    rw [integral_eq_lintegral_of_nonneg_ae t tt, ofReal_one, set_lintegral_one A]

  have hI : HasFiniteIntegral (A.indicator (fun (_ : Ω) ↦ (1 : ℝ))) μ := by
    unfold HasFiniteIntegral
    have : ∀ a, ‖A.indicator (fun (_ : Ω) ↦ (1 : ℝ)) a‖₊ = A.indicator (fun (_ : Ω) ↦ (1 : ℝ≥0∞)) a := by
      intro a
      by_cases ha : a ∈ A
      · rw [indicator_of_mem ha fun x ↦ 1, indicator_of_mem ha fun x ↦ 1, nnnorm_one]
        rfl
      rw [indicator_of_not_mem ha fun x ↦ 1, indicator_of_not_mem ha fun x ↦ 1, nnnorm_zero]
      rfl
    simp_rw [this]
    calc ∫⁻ a, A.indicator (fun x ↦ 1) a ∂μ = ∫⁻ a in A, 1 ∂μ :=
      lintegral_indicator (fun x ↦ 1) hAmΩ
    _ = μ A := set_lintegral_one A
    _ < ⊤ := measure_lt_top μ A

  have hAEmΩ : AEStronglyMeasurable (A.indicator (fun (_ : Ω) ↦ (1 : ℝ))) μ := by
    suffices StronglyMeasurable (A.indicator (fun (_ : Ω) ↦ (1 : ℝ))) by
      exact StronglyMeasurable.aestronglyMeasurable this
    exact StronglyMeasurable.mono hAE (sigma_generated_le hY)

  have : Integrable (A.indicator (fun (_ : Ω) ↦ (1 : ℝ))) μ := ⟨hAEmΩ, hI⟩

  have := ExpTotal.total_expectation_law this (sigma_generated_le hY) hAE

  unfold Measure.condProb
  rw [this]


  sorry
/- theorem total_expectation_law [IsProbabilityMeasure μ] (A : Set Ω)
    [SigmaFinite (μ.trim (sigma_generated_le hY))] (hm : StronglyMeasurable[gen_sigma Y] X) :
    (μ A).toReal = μ[μ.condProb A Y] :=
  (ExpTotal.total_expectation_law hX_i (sigma_generated_le hY) hm).symm -/

end TotalProba
