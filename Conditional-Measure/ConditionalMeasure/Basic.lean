import Mathlib.Probability.Kernel.Disintegration.Basic
open MeasureTheory Set ProbabilityTheory

section ProbTotalLaw

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

open MeasureTheory

variable {Ω F : Type*}
[NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
{m2 m1 mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → F}

namespace ExpCond

/- example (hm1 : m1 ≤ mΩ) (hm2 : m2 ≤ m1) : m2 ≤ mΩ := by exact fun s a ↦ hm1 s (hm2 s a)

example (hm1 : m1 ≤ mΩ) (hm2 : m2 ≤ m1) [SigmaFinite (μ.trim hm1)] :
    ∀ (s : Set Ω), MeasurableSet[m2] s → ∫ x in s, μ[X | m2] x ∂μ
    = ∫ x in s, μ[μ[X | m2] | m1] x ∂μ := by
  intro s hs
  exact (setIntegral_condexp hm1 (integrable_condexp) (hm2 s hs)).symm -/

theorem tower_property (hm1 : m1 ≤ mΩ) (hm2 : m2 ≤ m1) [SigmaFinite (μ.trim hm1)] :
    μ[X | m2] =ᵐ[μ] μ[μ[X | m2] | m1] := by
  have ae_mesu_m1 : AEStronglyMeasurable' m1 (μ[X | m2]) μ := by
    have ae_mesu_m2 : AEStronglyMeasurable' m2 (μ[X | m2]) μ :=
      StronglyMeasurable.aeStronglyMeasurable' (stronglyMeasurable_condexp)
    exact AEStronglyMeasurable'.mono ae_mesu_m2 hm2
  exact (condexp_of_aestronglyMeasurable' hm1 ae_mesu_m1 integrable_condexp).symm

/-
  TODO: create the sub σ-algebra {∅, Ω}.
-/



end ExpCond
