import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiperiodicDifferenceHolomorphic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiperiodic_difference_holomorphic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (f₁ f₂ : Pt E g → ℂ) (w₁ w₂ : E → Fin g → ℂ), IsOpen U → DifferentiableOn ℂ f₁ (cov U g) → DifferentiableOn ℂ f₂ (cov U g) → (∀ P ∈ cov U g, ∀ i : Fin g, f₁ (P.1, P.2 + Pi.single i 1) = f₁ P) → (∀ P ∈ cov U g, ∀ i : Fin g, f₂ (P.1, P.2 + Pi.single i 1) = f₂ P) → (∀ P ∈ cov U g, f₁ (P.1, P.2 + w₂ P.1) - f₁ P = f₂ (P.1, P.2 + w₁ P.1) - f₂ P) → ∀ b ∈ U, ∀ n : Fin g → ℤ, coef f₁ n b * (ch n (w₂ b) - 1) = coef f₂ n b * (ch n (w₁ b) - 1) := by
  first | exact @GlobalTheory.coef_mul_ch_sub_one_eq_of_translate_diff | exact GlobalTheory.coef_mul_ch_sub_one_eq_of_translate_diff | (intros; apply GlobalTheory.coef_mul_ch_sub_one_eq_of_translate_diff <;> assumption)
