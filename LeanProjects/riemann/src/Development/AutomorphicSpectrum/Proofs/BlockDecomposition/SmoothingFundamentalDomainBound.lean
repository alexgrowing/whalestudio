import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UfamConst
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

noncomputable section

namespace GlobalTheory.CompanionTheory.Conc

theorem lintegral_sq_le {Y : Type*} [MeasurableSpace Y] (P : Measure Y) [IsProbabilityMeasure P]
    (g : Y → ℝ≥0∞) (hg : AEMeasurable g P) : (∫⁻ y, g y ∂P) ^ 2 ≤ ∫⁻ y, g y ^ 2 ∂P := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hg
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at h
  have h2 := pow_le_pow_left' h 2
  have h3 : ((∫⁻ y, g y ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ))) ^ 2 = ∫⁻ y, g y ^ (2 : ℝ) ∂P := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  rw [h3] at h2
  simpa [ENNReal.rpow_ofNat] using h2

theorem enorm_sub_sm_sq_le (E : Type) [Field E] [NumberField E] (N : ℕ)
    [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)]
    (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (β : archGroup E N → ℝ) (hk : Ker ν β)
    (f : AdelicGLn.AdelicGL E N → ℂ) (hf : Continuous f) (x : AdelicGLn.AdelicGL E N) :
    ‖f x - sm ν β f x‖ₑ ^ 2 ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  have : IsProbabilityMeasure (ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hc1 : Continuous fun y => f (x * infEmb E N y) :=
    hf.comp (continuous_const.mul continuous_infEmb)
  have hi1 : Integrable (fun y => (β y : ℂ) * f (x * infEmb E N y)) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul hc1).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hi2 : Integrable (fun y => (β y : ℂ) * f x) ν :=
    ((Complex.continuous_ofReal.comp hk.cont).mul continuous_const).integrable_of_hasCompactSupport
      (hk.cpt.comp_left Complex.ofReal_zero |>.mul_right)
  have hmass : ∫ y, (β y : ℂ) * f x ∂ν = f x := by
    rw [integral_mul_const, integral_complex_ofReal, hk.mass]
    simp
  have heq : f x - sm ν β f x = ∫ y, (β y : ℂ) * (f x - f (x * infEmb E N y)) ∂ν := by
    simp only [mul_sub]
    rw [integral_sub hi2 hi1, hmass]
    rfl
  have hgm : Measurable fun y => ‖f (x * infEmb E N y) - f x‖ₑ :=
    (continuous_enorm.comp (hc1.sub continuous_const)).measurable
  have hle : ‖f x - sm ν β f x‖ₑ ≤ ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ
      ∂(ν.withDensity fun y => ENNReal.ofReal (β y)) := by
    rw [heq, lintegral_withDensity_eq_lintegral_mul ν hwm hgm]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    have hb : ‖(β y : ℂ)‖ₑ = ENNReal.ofReal (β y) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (hk.nonneg y)]
    rw [enorm_mul, hb, enorm_sub_rev]
    rfl
  exact (pow_le_pow_left' hle 2).trans (lintegral_sq_le _ _ hgm.aemeasurable)

end GlobalTheory.CompanionTheory.Conc

theorem GlobalTheory.CompanionTheory.Conc.smNear : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure] [MeasurableSpace (archGroup E N)] [BorelSpace (archGroup E N)] (ν : Measure (archGroup E N)) [ν.IsHaarMeasure] (F : Set (GA E N)) (β : archGroup E N → ℝ) (c : ℝ≥0∞), IsFundamentalDomain (latticeGL E N) F μ → Ker ν β →
  ∀ f : GA E N → ℂ, Continuous f → (∀ y ∈ tsupport β, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ≤ c) →
  ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ ≤ c := by
  intro E _ _ _ N _ _ μ _ _ _ ν _ F β c _ hk f hf hc
  have := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  have : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  have : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  have : SigmaCompactSpace (GA E N) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SFinite μ := inferInstance
  have hwm : Measurable fun y => ENNReal.ofReal (β y) := hk.cont.measurable.ennreal_ofReal
  set P : Measure (archGroup E N) := ν.withDensity fun y => ENNReal.ofReal (β y) with hP
  have : IsProbabilityMeasure P := by
    refine ⟨?_⟩
    rw [hP, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hk.cont.integrable_of_hasCompactSupport hk.cpt)
        (Eventually.of_forall hk.nonneg), hk.mass, ENNReal.ofReal_one]
  have hG : Continuous fun p : GA E N × archGroup E N => ‖f (p.1 * infEmb E N p.2) - f p.1‖ₑ ^ 2 :=
    (ENNReal.continuous_pow 2).comp (continuous_enorm.comp
      ((hf.comp (continuous_fst.mul (continuous_infEmb.comp continuous_snd))).sub
        (hf.comp continuous_fst)))
  have hae : ∀ᵐ y ∂P, y ∈ tsupport β := by
    rw [hP, ae_withDensity_iff hwm]
    refine Eventually.of_forall fun y hy => subset_tsupport _ ?_
    intro h0
    exact hy (by rw [h0, ENNReal.ofReal_zero])
  calc ∫⁻ x in F, ‖f x - sm ν β f x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x in F, ∫⁻ y, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂P ∂μ :=
        lintegral_mono fun x => enorm_sub_sm_sq_le E N ν β hk f hf x
    _ = ∫⁻ y, ∫⁻ x in F, ‖f (x * infEmb E N y) - f x‖ₑ ^ 2 ∂μ ∂P :=
        lintegral_lintegral_swap hG.measurable.aemeasurable
    _ ≤ ∫⁻ _, c ∂P := lintegral_mono_ae (hae.mono fun y hy => hc y hy)
    _ = c := by simp
