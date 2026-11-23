import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatFormMulPullZeroSection
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_form_mul_pull_zero_section : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}, IsPeriodMap B τ → (∀ n : ℤ, ∀ P ∈ cov B g, pull (mulN n) (om0 τ) P = ((n : ℝ) ^ 2) • om0 τ P) ∧ (∀ b ∈ B, (om0 τ (zeroSec g b)).compContinuousLinearMap (fderiv ℝ (zeroSec g) b) = 0) := by
  first | exact @GlobalTheory.Proof.flat_form_mul_pull_zero_section.main | exact GlobalTheory.Proof.flat_form_mul_pull_zero_section.main | (intros; apply GlobalTheory.Proof.flat_form_mul_pull_zero_section.main <;> assumption)
