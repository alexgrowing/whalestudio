import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.iwDens :
    ∀ (F : Type) [Field F] [NumberField F] (M₀ : Meas F), ∃ ρ : Measure (IdeleGroup F × G1 F), SFinite ρ ∧ (∀ u : G1 F → ℝ≥0∞, Measurable u → ∫⁻ p, u (mD p.1 * p.2) ∂ρ = M.J0 M₀ u) ∧ ∀ u : IdeleGroup F × G1 F → ℂ, (Integrable u ρ ↔ Integrable (fun p => (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p) M₀.ν) ∧ ∫ p, u p ∂ρ = ∫ p, (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p ∂M₀.ν := by
  intro F _ _ M₀
  have hfm : Measurable (fun p : IdeleGroup F × G1 F => Real.toNNReal ((ab p.1)⁻¹ ^ 2)) :=
    (((M.continuous_ab.measurable.comp measurable_fst).inv).pow_const 2).real_toNNReal
  have hwm : Measurable (fun p : IdeleGroup F × G1 F => M.wt p.1) :=
    M.measurable_wt.comp measurable_fst
  have hsm : ∀ (u : IdeleGroup F × G1 F → ℂ) (p : IdeleGroup F × G1 F),
      Real.toNNReal ((ab p.1)⁻¹ ^ 2) • u p = (((ab p.1)⁻¹ ^ 2 : ℝ) : ℂ) * u p := by
    intro u p
    rw [NNReal.smul_def, Real.coe_toNNReal _ (by positivity), Complex.real_smul]
  haveI : IsProbabilityMeasure M₀.κ := M₀.prob
  haveI : SFinite M₀.ν := by unfold Meas.ν; infer_instance
  refine ⟨M₀.ν.withDensity fun p => (Real.toNNReal ((ab p.1)⁻¹ ^ 2) : ℝ≥0∞), inferInstance, ?_, ?_⟩
  · intro u _
    have h := lintegral_withDensity_eq_lintegral_mul_non_measurable M₀.ν hwm
      (Eventually.of_forall fun p => ENNReal.ofReal_lt_top) (fun p => u (mD p.1 * p.2))
    exact h
  · intro u
    refine ⟨?_, ?_⟩
    · rw [integrable_withDensity_iff_integrable_smul hfm]
      simp only [hsm]
    · rw [integral_withDensity_eq_integral_smul hfm]
      simp only [hsm]
