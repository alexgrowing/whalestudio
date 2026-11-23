import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormFormBallIntegralScaling
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_form_ball_integral_scaling : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (t : Eˣ) (n : ℤ),
  ∫ u in (valBall E n : Set E), (χ (Algebra.norm F (t : E) * Algebra.norm F u) : ℂ) ∂muE E χ =
    (((modulus (Algebra.norm F (t : E)) : ℝ)⁻¹ : ℝ) : ℂ) *
      ∫ u in (valBall E (n + ord (t : E)) : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ := by
  first | exact @GlobalTheory.CompanionTheory.WeilGaussScale.integral_valBall_dilation | exact GlobalTheory.CompanionTheory.WeilGaussScale.integral_valBall_dilation | (intros; apply GlobalTheory.CompanionTheory.WeilGaussScale.integral_valBall_dilation <;> assumption)
