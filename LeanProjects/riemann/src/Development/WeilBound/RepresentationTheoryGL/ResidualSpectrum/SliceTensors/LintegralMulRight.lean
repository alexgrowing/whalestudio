import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.TwistedSlicesSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieDerivativeRealLieSmoothingEqDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CuspRep.CuspidalL2GL
open scoped ENNReal

namespace PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

theorem sq_lintegral_le {Y : Type*} [MeasurableSpace Y] (ρ : Measure Y) {g : Y → ℝ≥0∞} (hg : AEMeasurable g ρ) :
    (∫⁻ y, g y ∂ρ) ^ 2 ≤ ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ρ Real.HolderConjugate.two_two (f := fun _ => (1 : ℝ≥0∞))
    aemeasurable_const hg
  simp only [ENNReal.one_rpow, lintegral_const] at h
  calc (∫⁻ y, g y ∂ρ) ^ 2 ≤ (ρ Set.univ ^ (1 / 2 : ℝ) * (∫⁻ y, g y ^ (2 : ℝ) ∂ρ) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        simpa [Pi.mul_apply] using h
    _ = ρ Set.univ * ∫⁻ y, g y ^ 2 ∂ρ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (_ ^ (1 / 2 : ℝ)), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

theorem lintegral_sq_lt_top {μ : Measure (GA E N)} [μ.IsHaarMeasure] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) : ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ < ⊤ := by
  have hm := ((memL2_iff_fundamental_domain (isFundamentalDomain_stdDom (latticeGL E N) μ)).1 h).2
  have := hm.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  simpa using this

theorem lintegral_mul_right {μ : Measure (GA E N)} [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ : GA E N → ℂ}
    (h : MemL2Quotient (latticeGL E N) μ φ) (g : GA E N) :
    ∫⁻ x in stdDom (latticeGL E N), ‖φ (x * g)‖ₑ ^ 2 ∂μ = ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have hm : AEMeasurable (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2) (quotMeasure (latticeGL E N) μ) :=
    h.2.1.enorm.pow_const 2
  have e1 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ q‖ₑ ^ 2)
  have e2 := lintegral_quotMeasure hd (fun q => ‖descend (latticeGL E N) φ (rmul (latticeGL E N) g q)‖ₑ ^ 2)
  simp only [rmul_mk, h.1.descend_mk] at e1 e2
  rw [← e1, ← e2]
  have hp := measurePreserving_rmul (Γ := latticeGL E N) (μ := μ) g
  conv_rhs => rw [← hp.map_eq]
  rw [lintegral_map' (by rwa [hp.map_eq]) (measurable_rmul g).aemeasurable]

theorem memL2_of_smoothing (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (ν : Measure (Lie E N))
    [ν.IsAddHaarMeasure] {α : Lie E N → ℂ} (hα : GlobalTheory.CuspQuot.IsTest (invSet E N) α) {φ : GA E N → ℂ}
    (hc : Continuous φ) (h : MemL2Quotient (latticeGL E N) μ φ) :
    MemL2Quotient (latticeGL E N) μ (GlobalTheory.CuspQuot.smoothing ν α φ) := by
  have hd := isFundamentalDomain_stdDom (latticeGL E N) μ
  have : ProperSpace (Lie E N) := FiniteDimensional.proper ℝ _
  have : SigmaFinite ν := Measure.IsAddHaarMeasure.sigmaFinite ν
  have hl : LeftInv (latticeGL E N) φ := h.1
  have hlS : LeftInv (latticeGL E N) (GlobalTheory.CuspQuot.smoothing ν α φ) := fun γ hγ g => by
    simp only [GlobalTheory.CuspQuot.smoothing, chart, mul_assoc, hl γ hγ]
  have hH : Continuous fun p : GA E N × Lie E N => α p.2 * chart φ p.1 p.2 :=
    GlobalTheory.CuspQuot.continuous_integrand hα hc
  have hmS : AEStronglyMeasurable (GlobalTheory.CuspQuot.smoothing ν α φ) (μ.restrict (stdDom (latticeGL E N))) :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := ν)).aestronglyMeasurable
  set K := tsupport α with hKdef
  have hKν : ν K < ⊤ := hα.2.1.isCompact.measure_lt_top
  have hpt : ∀ x, ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by
    intro x
    have h1 : ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ≤ ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν := by
      rw [setLIntegral_eq_of_support_subset]
      · exact enorm_integral_le_lintegral_enorm _
      · intro y hy
        by_contra hyK
        apply hy
        simp [image_eq_zero_of_notMem_tsupport hyK]
    have hx : Continuous fun y => α y * chart φ x y := hH.comp (continuous_const.prodMk continuous_id)
    have h2 := sq_lintegral_le (ν.restrict K) (g := fun y => ‖α y * chart φ x y‖ₑ) hx.enorm.aemeasurable
    rw [Measure.restrict_apply_univ] at h2
    calc _ ≤ (∫⁻ y in K, ‖α y * chart φ x y‖ₑ ∂ν) ^ 2 := by gcongr
      _ ≤ ν K * ∫⁻ y in K, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := h2
      _ ≤ ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν := by gcongr; exact Measure.restrict_le_self
  set I := ∫⁻ x in stdDom (latticeGL E N), ‖φ x‖ₑ ^ 2 ∂μ with hIdef
  have hI : I < ⊤ := lintegral_sq_lt_top h
  have hin : ∀ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ = ‖α y‖ₑ ^ 2 * I := by
    intro y
    by_cases hy : IsUnit (Matrix.of y)
    · simp_rw [chart, dif_pos hy, enorm_mul, mul_pow]
      rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_right h]
    · have : α y = 0 := image_eq_zero_of_notMem_tsupport fun h' => hy (hα.2.2 h')
      simp [this]
  have hα2 : ∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν < ⊤ := by
    have hmα := hα.1.continuous.memLp_of_hasCompactSupport (p := 2) (μ := ν) hα.2.1
    have := hmα.2
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
    simpa using this
  have hmeas : AEMeasurable (Function.uncurry fun x y => ‖α y * chart φ x y‖ₑ ^ 2)
      ((μ.restrict (stdDom (latticeGL E N))).prod ν) :=
    ((ENNReal.continuous_pow 2).comp hH.enorm).measurable.aemeasurable
  refine (memL2_iff_fundamental_domain hd).2 ⟨hlS, hmS, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc ∫⁻ x in stdDom (latticeGL E N), ‖GlobalTheory.CuspQuot.smoothing ν α φ x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in stdDom (latticeGL E N), ν K * ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ := lintegral_mono hpt
    _ = ν K * ∫⁻ x in stdDom (latticeGL E N), ∫⁻ y, ‖α y * chart φ x y‖ₑ ^ 2 ∂ν ∂μ :=
        lintegral_const_mul' _ _ hKν.ne
    _ = ν K * ∫⁻ y, ∫⁻ x in stdDom (latticeGL E N), ‖α y * chart φ x y‖ₑ ^ 2 ∂μ ∂ν := by
        rw [lintegral_lintegral_swap hmeas]
    _ = ν K * ((∫⁻ y, ‖α y‖ₑ ^ 2 ∂ν) * I) := by
        simp_rw [hin]
        rw [lintegral_mul_const' _ _ hI.ne]
    _ < ⊤ := ENNReal.mul_lt_top hKν (ENNReal.mul_lt_top hα2 hI)

end PositivityTheory.Rg.Rs.SmoothingSquareIntegrable

end
