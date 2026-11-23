import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralIwasawaMajorantFinite
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaIntegralRightTranslateInvariantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralDetSecondVectorFiniteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFiniteStatement
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_iwasawa_majorant_finite : ForS fun F _ _ _ _ _ _ ψ => ∀ R B σ ε : ℝ, 0 < ε → 2 * ε < σ → ε < 1 / 2 →
  ∫⁻ g, ENNReal.ofReal ((modulus (g.val).det : ℝ) ^ (σ + 1 / 2)) *
    ∫⁻ p, ENNReal.ofReal (wR p) * ENNReal.ofReal (Mj R B σ ε g p) ∂mIw ψ ∂LFS.hG ψ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.ZetaIntegralBound.outer_finite | exact GlobalTheory.CompanionTheory.ZetaIntegralBound.outer_finite | (intros; apply GlobalTheory.CompanionTheory.ZetaIntegralBound.outer_finite <;> assumption)
