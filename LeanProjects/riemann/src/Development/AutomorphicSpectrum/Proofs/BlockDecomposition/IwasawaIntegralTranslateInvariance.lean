import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableIwasawaPullback
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFiniteStatement
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RInvB

theorem integral_right_invariant : ForS fun F _ _ _ _ _ _ ψ => ∀ B : GL (Fin 2) F → ℂ, Continuous B →
    (∀ x h, B (uni2 x * h) = B h) →
    ∀ g : GL (Fin 2) F, ∫ p, ((wR p : ℝ) : ℂ) * B (hI p * g) ∂mIw ψ =
      ∫ p, ((wR p : ℝ) : ℂ) * B (hI p) ∂mIw ψ := by
  intro F _ _ _ _ _ _ ψ hψ B hB hN g
  have hl := GlobalTheory.T.iwasawa_integral_right_translate_invariant F ψ hψ
  have hd : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => ENNReal.ofReal (wR p) :=
    GlobalTheory.CompanionTheory.BochIw.measurable_wR'.ennreal_ofReal
  have hlt : ∀ᵐ p ∂mIw ψ, ENNReal.ofReal (wR p) < ⊤ := ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have hT1 : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => B (hI p) :=
    (hB.comp GlobalTheory.CompanionTheory.BochIw.cont_hI).measurable
  have hTg : Measurable fun p : Fˣ × Fˣ × GL (Fin 2) F => B (hI p * g) :=
    (hB.comp (GlobalTheory.CompanionTheory.BochIw.cont_hI.mul continuous_const)).measurable
  have hmap : Measure.map (fun p => B (hI p * g))
        ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p)) =
      Measure.map (fun p => B (hI p)) ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p)) := by
    ext S hS
    have hind : ∀ (T : Fˣ × Fˣ × GL (Fin 2) F → ℂ) (p : Fˣ × Fˣ × GL (Fin 2) F),
        (T ⁻¹' S).indicator (fun p => ENNReal.ofReal (wR p)) p =
          ENNReal.ofReal (wR p) * S.indicator (1 : ℂ → ENNReal) (T p) := fun T p => by
      by_cases hp : T p ∈ S
      · have hp' : p ∈ T ⁻¹' S := hp
        simp [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
      · have hp' : p ∉ T ⁻¹' S := hp
        simp [Set.indicator_of_notMem hp', Set.indicator_of_notMem hp]
    have key := hl (fun h => S.indicator (1 : ℂ → ENNReal) (B h))
      ((measurable_one.indicator hS).comp hB.measurable) (fun x h => by simp only [hN]) g
    rw [Measure.map_apply hTg hS, Measure.map_apply hT1 hS, withDensity_apply _ (hTg hS),
      withDensity_apply _ (hT1 hS), ← lintegral_indicator (hTg hS), ← lintegral_indicator (hT1 hS)]
    simp only [hind]
    exact key
  have e : ∀ T : Fˣ × Fˣ × GL (Fin 2) F → ℂ, Measurable T →
      ∫ p, ((wR p : ℝ) : ℂ) * T p ∂mIw ψ =
        ∫ z, z ∂(Measure.map T ((mIw ψ).withDensity fun p => ENNReal.ofReal (wR p))) := by
    intro T hT
    rw [integral_map (f := fun z : ℂ => z) hT.aemeasurable aestronglyMeasurable_id,
      integral_withDensity_eq_integral_toReal_smul hd hlt]
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    simp only [ENNReal.toReal_ofReal (GlobalTheory.CompanionTheory.BochIw.wR_pos' p).le, Complex.real_smul]
  rw [e _ hTg, e _ hT1, hmap]

end GlobalTheory.CompanionTheory.RInvB
