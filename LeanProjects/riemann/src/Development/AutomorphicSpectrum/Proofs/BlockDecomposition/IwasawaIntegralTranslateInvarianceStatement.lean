import Mathlib
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralTranslateInvariance
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

theorem _root_.GlobalTheory.T.iwasawa_integral_translate_invariance : ForS fun F _ _ _ _ _ _ ψ => ∀ B : GL (Fin 2) F → ℂ, Continuous B → (∀ x h, B (uni2 x * h) = B h) →
  ∀ g : GL (Fin 2) F, ∫ p, ((wR p : ℝ) : ℂ) * B (hI p * g) ∂mIw ψ = ∫ p, ((wR p : ℝ) : ℂ) * B (hI p) ∂mIw ψ := by
  first | exact @GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | exact GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | (intros; apply GlobalTheory.CompanionTheory.RInvB.integral_right_invariant <;> assumption) | exact @GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | exact GlobalTheory.CompanionTheory.RInvB.integral_right_invariant | (intros; apply GlobalTheory.CompanionTheory.RInvB.integral_right_invariant <;> assumption)
