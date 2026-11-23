import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory

theorem integrable_inner_rpow_avg_left : ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → ∀ (p : ℝ), 1 ≤ p → ∀ φ : KG ε → ℂ, Continuous φ → ∀ u u' : U, Integrable (fun g => ‖⟪u', π g u⟫_ℂ‖ ^ p) μ → Integrable (fun g => ‖⟪∫ k, φ k • π k u' ∂(muK ε), π g u⟫_ℂ‖ ^ p) μ := by
  intro n ε μ _ U _ _ _ π hπ p hp φ hφ u u' hf
  have hp0 : (0:ℝ) ≤ p := by linarith
  set f : ↥(UJ ε) → ℂ := fun g => ⟪u', π g u⟫_ℂ with hfdef
  have hfc : Continuous f := continuous_const.inner (hπ.continuous_apply u)
  have key : ∀ z : ℂ, ‖(‖z‖ ^ p)‖ₑ = ‖z‖ₑ ^ p := by
    intro z
    rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0,
      ofReal_norm_eq_enorm]
  have hI : ∫⁻ g, ‖f g‖ₑ ^ p ∂μ < ∞ := by
    have h2 := hf.2
    unfold HasFiniteIntegral at h2
    simpa only [key] using h2
  have hinner : ∀ (a b : U) (g : ↥(UJ ε)), ⟪π g a, π g b⟫_ℂ = ⟪a, b⟫_ℂ := by
    intro a b g
    let L : U →ₗᵢ[ℂ] U := { toLinearMap := ((π g : U →L[ℂ] U) : U →ₗ[ℂ] U), norm_map' := hπ.norm_apply g }
    exact L.inner_map_map a b
  have hshift : ∀ (g : ↥(UJ ε)) (k : ↥(KG ε)),
      ‖⟪π g u, π (k : ↥(UJ ε)) u'⟫_ℂ‖ = ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ := by
    intro g k
    have h1 : π g u = π (k : ↥(UJ ε)) (π ((k : ↥(UJ ε))⁻¹ * g) u) := by
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel_left]
    rw [h1, hinner, norm_inner_symm]
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  set v := ∫ k, φ k • π (k : ↥(UJ ε)) u' ∂(muK ε) with hv
  have hint : Integrable (fun k : ↥(KG ε) => φ k • π (k : ↥(UJ ε)) u') (muK ε) := by
    have hc : Continuous (fun k : ↥(KG ε) => φ k • π (k : ↥(UJ ε)) u') :=
      hφ.smul ((hπ.continuous_apply u').comp continuous_subtype_val)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ g, ‖⟪v, π g u⟫_ℂ‖ₑ ≤
      ENNReal.ofReal C * ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ∂(muK ε) := by
    intro g
    have e1 : ‖⟪v, π g u⟫_ℂ‖ₑ = ‖∫ k, ⟪π g u, φ k • π (k : ↥(UJ ε)) u'⟫_ℂ ∂(muK ε)‖ₑ := by
      rw [integral_inner hint, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_inner_symm]
    rw [e1, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun k => ?_)
    rw [inner_smul_right, enorm_mul, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm (f _),
      ← ofReal_norm_eq_enorm, hshift]
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    refine le_of_le_of_eq (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hC k (Set.mem_univ _)) (norm_nonneg (f ((k : ↥(UJ ε))⁻¹ * g))))) ?_
    exact ENNReal.ofReal_mul' (norm_nonneg _)
  have hJ : ∀ g, (∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ∂(muK ε)) ^ p ≤
      ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) := by
    intro g
    have hm : AEStronglyMeasurable (fun k : ↥(KG ε) => f ((k : ↥(UJ ε))⁻¹ * g)) (muK ε) :=
      (hfc.comp ((continuous_subtype_val.inv).mul continuous_const)).aestronglyMeasurable
    have h1 := eLpNorm_le_eLpNorm_of_exponent_le (μ := muK ε) (p := 1) (q := ENNReal.ofReal p)
      (by simpa using hp) hm
    rw [eLpNorm_one_eq_lintegral_enorm,
      eLpNorm_eq_lintegral_rpow_enorm (by simp; linarith) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hp0, one_div] at h1
    exact (ENNReal.le_rpow_inv_iff (by linarith)).1 h1
  refine ⟨(Continuous.aestronglyMeasurable ?_), ?_⟩
  · exact ((continuous_const.inner (hπ.continuous_apply u)).norm).rpow_const (fun _ => Or.inr hp0)
  unfold HasFiniteIntegral
  simp only [key]
  have hmeas : AEMeasurable (Function.uncurry fun (g : ↥(UJ ε)) (k : ↥(KG ε)) =>
      ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p) (μ.prod (muK ε)) := by
    have hc : Continuous (fun x : ↥(UJ ε) × ↥(KG ε) => f ((x.2 : ↥(UJ ε))⁻¹ * x.1)) :=
      hfc.comp ((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst)
    exact (hc.measurable.enorm.pow_const p).aemeasurable
  have hCp : ENNReal.ofReal C ^ p ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  calc ∫⁻ g, ‖⟪v, π g u⟫_ℂ‖ₑ ^ p ∂μ
      ≤ ∫⁻ g, ENNReal.ofReal C ^ p * ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) ∂μ := by
        refine lintegral_mono fun g => (ENNReal.rpow_le_rpow (hpt g) hp0).trans ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
        gcongr
        exact hJ g
    _ = ENNReal.ofReal C ^ p * ∫⁻ g, ∫⁻ k, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂(muK ε) ∂μ :=
        lintegral_const_mul' _ _ hCp
    _ = ENNReal.ofReal C ^ p * ∫⁻ k, ∫⁻ g, ‖f ((k : ↥(UJ ε))⁻¹ * g)‖ₑ ^ p ∂μ ∂(muK ε) := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ENNReal.ofReal C ^ p * ∫⁻ k : ↥(KG ε), ∫⁻ g, ‖f g‖ₑ ^ p ∂μ ∂(muK ε) := by
        congr 1
        refine lintegral_congr fun k => ?_
        exact lintegral_mul_left_eq_self (fun g => ‖f g‖ₑ ^ p) _
    _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top hCp.lt_top (ENNReal.mul_lt_top hI (measure_lt_top _ _))

end GlobalTheory
