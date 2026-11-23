import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.TypeFin
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.SummandsContRep

open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section General

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ] [SFinite μ]

private theorem rconv_fix (ν : Measure G) [IsProbabilityMeasure ν] {U : Set G} (hU : IsCompact U)
    (hs : ∀ᵐ k ∂ν, k ∈ U) {e : G → ℂ} (he : Continuous e)
    (a : CompactlySupportedContinuousMap G ℂ) (hH : ∀ g, ∫ k, e k * a (k⁻¹ * g) ∂ν = a g)
    (y : Lp ℂ 2 (quotientMeasure Γ μ)) (g : G) :
    ∫ k, e k * rconv Γ μ a y (g * k) ∂ν = rconv Γ μ a y g := by
  set L : G → ℂ := fun h => y (mk Γ h) with hL
  set P : G × G → ℂ := fun p => e p.1 * a (p.1⁻¹ * (g⁻¹ * p.2)) with hP
  have hPc : Continuous P := by
    have h1 : Continuous fun p : G × G => a (p.1⁻¹ * (g⁻¹ * p.2)) :=
      a.continuous.comp (by fun_prop)
    exact (he.comp continuous_fst).mul h1
  obtain ⟨M, hM⟩ := hU.exists_bound_of_continuousOn he.continuousOn
  obtain ⟨A, hA⟩ := a.continuous.bounded_above_of_compact_support a.hasCompactSupport
  set C : Set G := (fun p : G × G => g * (p.1 * p.2)) '' (U ×ˢ tsupport (a : G → ℂ)) with hCdef
  have hC : IsCompact C := (hU.prod a.hasCompactSupport.isCompact).image (by fun_prop)
  have hint : Integrable (fun p : G × G => P p * L p.2) (ν.prod μ) := by
    have hB : Integrable (fun p : G × G => (M * A) * C.indicator (fun h => ‖L h‖) p.2)
        (ν.prod μ) := by
      have h0 : Integrable (C.indicator fun h => ‖L h‖) μ :=
        (integrable_indicator_iff hC.measurableSet).2 (integrableOn_lift Γ μ y hC).norm
      exact (h0.comp_snd ν).const_mul _
    refine hB.mono' (hPc.aestronglyMeasurable.mul
      ((stronglyMeasurable_lift Γ μ y).comp_measurable measurable_snd).aestronglyMeasurable) ?_
    have hk : ∀ᵐ p ∂(ν.prod μ), p.1 ∈ U :=
      Measure.quasiMeasurePreserving_fst.ae hs
    filter_upwards [hk] with p hp
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM p.1 hp)
    by_cases hz : p.1⁻¹ * (g⁻¹ * p.2) ∈ tsupport (a : G → ℂ)
    · have hmem : p.2 ∈ C := ⟨(p.1, p.1⁻¹ * (g⁻¹ * p.2)), ⟨hp, hz⟩, by simp⟩
      rw [indicator_of_mem hmem, norm_mul, norm_mul]
      have hA' := hA (p.1⁻¹ * (g⁻¹ * p.2))
      exact mul_le_mul_of_nonneg_right (mul_le_mul (hM p.1 hp) hA' (norm_nonneg _) hM0) (norm_nonneg _)
    · have h0 : a (p.1⁻¹ * (g⁻¹ * p.2)) = 0 := image_eq_zero_of_notMem_tsupport hz
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1)
      simp only [hP, h0, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg hM0 hA0) (indicator_nonneg (fun _ _ => norm_nonneg _) _)
  calc ∫ k, e k * rconv Γ μ a y (g * k) ∂ν
      = ∫ k, ∫ h, P (k, h) * L h ∂μ ∂ν := by
        refine integral_congr_ae (Eventually.of_forall fun k => ?_)
        simp only [rconv, hP, hL]
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        simp only [mul_inv_rev, mul_assoc]
    _ = ∫ h, ∫ k, P (k, h) * L h ∂ν ∂μ := integral_integral_swap (f := fun k h => P (k, h) * L h) hint
    _ = ∫ h, a (g⁻¹ * h) * L h ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        simp only [hP]
        rw [integral_mul_const, hH (g⁻¹ * h)]
    _ = rconv Γ μ a y g := rfl

end General

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.KX.fixRep :
    ∀ {K : Type} [Field K] [NumberField K] {n : ℕ} (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (D : TypeDat K n) (a : CC K n), D.Hecke a →
      ∀ (y : L2 μ) (Φ : G1 K n → ℂ), Continuous Φ → Reps μ (Rop μ a y) Φ → D.Fix Φ := by
  intro K _ _ n μ _ D a hH y Φ hΦ hrep g
  haveI := D.prob
  have hc := isContRep_rconv μ a y
  have hEq : Φ = rconv (Gam K n) μ a y := by
    refine (hΦ.ae_eq_iff_eq μ hc.1).1 ?_
    exact Filter.EventuallyEq.trans (Filter.EventuallyEq.symm hrep) hc.2.2
  rw [hEq]
  exact rconv_fix (Gam K n) μ D.ν (typeFin D).1 D.supp D.cont a (fun g => (hH g).1) y g
