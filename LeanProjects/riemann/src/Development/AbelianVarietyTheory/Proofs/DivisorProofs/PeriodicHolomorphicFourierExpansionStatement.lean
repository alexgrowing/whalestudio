import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicFourierExpansion
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_holomorphic_fourier_expansion : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ h (cov U g) → (∀ P ∈ cov U g, ∀ i : Fin g, h (P.1, P.2 + Pi.single i 1) = h P) → ∀ P ∈ cov U g, HasSum (fun n : Fin g → ℤ => coef h n P.1 * ch n P.2) (h P) := by
  first | exact @GlobalTheory.FamilyFourier.hasSum_coef_mul_ch | exact GlobalTheory.FamilyFourier.hasSum_coef_mul_ch | (intros; apply GlobalTheory.FamilyFourier.hasSum_coef_mul_ch <;> assumption)
