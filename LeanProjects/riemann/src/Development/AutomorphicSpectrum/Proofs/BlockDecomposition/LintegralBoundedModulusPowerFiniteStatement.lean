import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralBoundedModulusPowerFinite
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WhittakerFunctionalEquationAdditive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Aq
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.DampedZetaMajorant GlobalTheory.CompanionTheory.GL2Unfolding GlobalTheory.CompanionTheory.GJTwo
open scoped ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_bounded_modulus_power_finite : ForS fun F _ _ _ _ _ _ _ => ∀ B e : ℝ, 0 < e →
  ∫⁻ a : Fˣ, Set.indicator {a : Fˣ | (modulus (a : F) : ℝ) ≤ B} (fun a => ENNReal.ofReal ((modulus (a : F) : ℝ) ^ e)) a ∂multHaar F < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top | exact GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top | (intros; apply GlobalTheory.CompanionTheory.MHInt.lintegral_indicator_modulus_rpow_lt_top <;> assumption)
