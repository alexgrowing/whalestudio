import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientHolomorphicInBase
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_holomorphic_in_base : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ h (cov U g) → ∀ n : Fin g → ℤ, DifferentiableOn ℂ (coef h n) U := by
  first | exact @GlobalTheory.differentiableOn_coef_of_holomorphic | exact GlobalTheory.differentiableOn_coef_of_holomorphic | (intros; apply GlobalTheory.differentiableOn_coef_of_holomorphic <;> assumption)
