import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFinite
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_det_second_vector_finite : ForS fun F _ _ _ _ _ _ ψ => ∀ R c t : ℝ, 1 < c → 0 ≤ t → t < c →
  ∫⁻ g, Set.indicator {g : GL (Fin 2) F | ∀ i j, (modulus (g.val i j) : ℝ) ≤ R}
    (fun g => ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ c * mx (e2r g) ^ (-t))) g ∂LFS.hG ψ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SingInt.lintegral_det_mx_lt_top | exact GlobalTheory.CompanionTheory.SingInt.lintegral_det_mx_lt_top | (intros; apply GlobalTheory.CompanionTheory.SingInt.lintegral_det_mx_lt_top <;> assumption)
