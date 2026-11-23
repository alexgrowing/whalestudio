import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientExponentialDecayLocal
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coefficient_exponential_decay_local : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ h (cov U g) → (∀ P ∈ cov U g, ∀ i : Fin g, h (P.1, P.2 + Pi.single i 1) = h P) → ∀ b₀ ∈ U, ∀ z₀ : Fin g → ℂ, ∃ t ∈ nhds ((b₀, z₀) : Pt E g), ∃ C : ℝ, ∀ n : Fin g → ℤ, ∀ P ∈ t, ‖coef h n P.1 * ch n P.2‖ ≤ C * Real.exp (-(2 * π * ∑ i, |(n i : ℝ)|)) := by
  first | exact @GlobalTheory.FamilyFourier.Decay.exists_nhds_norm_coef_mul_ch_le | exact GlobalTheory.FamilyFourier.Decay.exists_nhds_norm_coef_mul_ch_le | (intros; apply GlobalTheory.FamilyFourier.Decay.exists_nhds_norm_coef_mul_ch_le <;> assumption)
