import Mathlib
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormIntegralFourierFactorization

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
theorem _root_.GlobalTheory.T.norm_form_integral_fourier_factorization : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ := by
  first | exact @GlobalTheory.CompanionTheory.WeilSquare.gauss_core | exact GlobalTheory.CompanionTheory.WeilSquare.gauss_core | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.gauss_core <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.gauss_core | exact GlobalTheory.CompanionTheory.WeilSquare.gauss_core | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.gauss_core <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.core_of_haar | exact GlobalTheory.CompanionTheory.WeilSquare.core_of_haar | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.core_of_haar <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add | exact GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.setIntegral_ball_add <;> assumption) | exact @GlobalTheory.CompanionTheory.WeilSquare.square_identity | exact GlobalTheory.CompanionTheory.WeilSquare.square_identity | (intros; apply GlobalTheory.CompanionTheory.WeilSquare.square_identity <;> assumption)
