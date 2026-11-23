import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionFunctionInjectiveOfPolynomialGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowthStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QExpansionPolyGrowthSummableContinuousStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasModerateGrowthQExpansionOfCoeffPolynomialGrowStatement

open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.PetPos

theorem volume_isOpenPosMeasure : (volume : Measure ℍ).IsOpenPosMeasure := by
  have h0 : (volume.comap UpperHalfPlane.coe : Measure ℍ).IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap _ UpperHalfPlane.isOpenEmbedding_coe
  have hm : Continuous fun z : ℍ => (NNReal.mk z.im z.im_pos.le : NNReal) :=
    UpperHalfPlane.continuous_im.subtype_mk _
  have hc : Continuous fun z : ℍ => ((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) :=
    (continuous_const.div₀ hm (fun x => NNReal.ne_iff.mp x.im_ne_zero)).pow 2
  refine ⟨fun U hU hne => ?_⟩
  rw [UpperHalfPlane.volume_def, withDensity_apply _ hU.measurableSet]
  refine ne_of_gt ?_
  have hmeas : Measurable fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal) :=
    (ENNReal.continuous_coe.comp hc).measurable
  rw [setLIntegral_pos_iff hmeas]
  have hsupp : Function.support (fun z : ℍ =>
      (((1 / NNReal.mk z.im z.im_pos.le : NNReal) ^ 2 : NNReal) : ENNReal)) = Set.univ := by
    ext z
    simp [z.im_ne_zero]
    intro h
    have h' := congrArg Subtype.val h
    simp [z.im_ne_zero] at h'
  rw [hsupp, Set.univ_inter]
  exact hU.measure_pos _ hne

theorem norm_ch_eq_one {L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) (γ : SL(2, ℤ))
    (hγ : (L : ℤ) ∣ γ 1 0) : ‖ch ε (γ 1 1)‖ = 1 := by
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_trans (Int.natCast_dvd_natCast.mpr hNL) hγ
  have h1 : ((γ 1 1 : ℤ) : ZMod N) * ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have h := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at h
    rw [hc, mul_zero, sub_zero] at h
    rw [mul_comm]
    exact h
  obtain ⟨u, hu⟩ := IsUnit.of_mul_eq_one _ h1
  show ‖ε ((γ 1 1 : ℤ) : ZMod N)‖ = 1
  rw [← hu]
  exact DirichletCharacter.unit_norm_eq_one ε u

theorem norm_sq_mul_im_pow_smul {k L N : ℕ} (ε : DirichletCharacter ℂ N) (hNL : N ∣ L) {f : ℍ → ℂ}
    (hf : Inv k L (ch ε) f) (γ : SL(2, ℤ)) (hγ : (L : ℤ) ∣ γ 1 0) (τ : ℍ) :
    ‖f (γ • τ)‖ ^ 2 * (γ • τ).im ^ k = ‖f τ‖ ^ 2 * τ.im ^ k := by
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← ModularGroup.denom_apply]
    exact UpperHalfPlane.denom_ne_zero _ _
  have hpos : 0 < ‖((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)‖ := norm_pos_iff.mpr hD
  rw [hf γ hγ τ, ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, norm_mul, norm_mul,
    norm_ch_eq_one ε hNL γ hγ, one_mul, norm_pow, div_pow, Complex.normSq_eq_norm_sq]
  field_simp
  ring

theorem pet_self_ne_zero : ∀ (k L N : ℕ) (ε : DirichletCharacter ℂ N) (ρ : ℍ → ℝ) (h : ℕ → ℂ), 1 ≤ k → 0 < L → N ∣ L →
    Wt L ρ → CF k L (ch ε) h → h ≠ 0 → pet k ρ (qs h) (qs h) ≠ 0 := by
  intro k L N ε ρ h hk hL hN hW hCF hh
  haveI : (volume : Measure ℍ).IsOpenPosMeasure := volume_isOpenPosMeasure
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  haveI : Countable SL(2, ℤ) :=
    inferInstanceAs (Countable {A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1})
  have hP : PolyB h := hCF.1.1
  have hInv : Inv k L (ch ε) (qs h) := hCF.1.2
  have hqc : Continuous (qs h) := (GlobalTheory.T.qExpansion_polyGrowth_summable_continuous h hP).2
  set Φ : ℍ → ℝ := fun τ => ‖qs h τ‖ ^ 2 * τ.im ^ k with hΦ
  set G : ℍ → ℝ := fun τ => ρ τ * Φ τ with hG
  have hΦc : Continuous Φ := (hqc.norm.pow 2).mul (UpperHalfPlane.continuous_im.pow k)
  have hGnn : 0 ≤ G := fun τ => mul_nonneg (hW.nonneg τ) (by positivity)
  have heq : (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs h τ) * qs h τ * (τ.im : ℂ) ^ k)) =
      fun τ => ((G τ : ℝ) : ℂ) := by
    funext τ
    rw [Complex.conj_mul']
    simp only [hG, hΦ]
    push_cast
    ring
  have hint := GlobalTheory.T.integrable_petersson_integrand_moderateGrowth k L L N ε h ρ (qs h) hk hL hN hW hCF hqc.aestronglyMeasurable
    (GlobalTheory.T.hasModerateGrowth_qExpansion_of_coeffPolynomialGrowth h hP)
  rw [heq] at hint
  have hGi : Integrable G := by
    have := hint.re
    simpa using this
  intro hzero
  have hpet : pet k ρ (qs h) (qs h) = ((∫ τ, G τ : ℝ) : ℂ) := by
    unfold pet
    rw [heq, integral_complex_ofReal]
  rw [hpet, Complex.ofReal_eq_zero, integral_eq_zero_iff_of_nonneg hGnn hGi] at hzero
  have hmp : ∀ γ : SL(2, ℤ), MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    intro γ
    have hm := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
    convert hm using 1
    ext z
    simp
  have hall : ∀ᵐ τ ∂(volume : Measure ℍ), ∀ γ : Gamma0 L, G ((γ : SL(2, ℤ)) • τ) = 0 := by
    rw [ae_all_iff]
    intro γ
    have h1 := (hmp (γ : SL(2, ℤ))).quasiMeasurePreserving.ae_eq_comp hzero
    filter_upwards [h1] with τ hτ
    simpa using hτ
  have hΦ0 : Φ =ᵐ[volume] 0 := by
    filter_upwards [hall] with τ hτ
    have hterm : ∀ γ : Gamma0 L, Φ τ * ρ ((γ : SL(2, ℤ)) • τ) = 0 := by
      intro γ
      have hγL : (L : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (CongruenceSubgroup.Gamma0_mem.mp γ.2)
      have hinv := norm_sq_mul_im_pow_smul ε hN hInv (γ : SL(2, ℤ)) hγL τ
      have h2 := hτ γ
      simp only [hG, hΦ] at h2 ⊢
      rw [hinv] at h2
      rw [mul_comm]
      exact h2
    have hs := (hW.sum τ).mul_left (Φ τ)
    simp only [hterm, mul_one] at hs
    exact hs.unique hasSum_zero
  have hΦz : Φ = 0 := (Continuous.ae_eq_iff_eq volume hΦc continuous_const).mp hΦ0
  apply hh
  have hq0 : qs h = qs 0 := by
    funext τ
    have h3 := congrFun hΦz τ
    simp only [hΦ, Pi.zero_apply] at h3
    have him : τ.im ^ k ≠ 0 := pow_ne_zero _ τ.im_ne_zero
    have h4 : ‖qs h τ‖ ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_right him
    have h5 : qs h τ = 0 := by simpa using h4
    rw [h5]
    simp [qs]
  exact GlobalTheory.T.qExpansionFunction_injective_of_polynomialGrowth h 0 hP ⟨0, 0, fun n => by simp⟩ hq0

end GlobalTheory.EisM.PetPos
