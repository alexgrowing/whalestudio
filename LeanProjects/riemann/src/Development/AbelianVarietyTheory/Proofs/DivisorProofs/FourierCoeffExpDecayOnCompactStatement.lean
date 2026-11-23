import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoeffExpDecayOnCompact
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegL1Norm
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TauPeriod Complex
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_coeff_exp_decay_on_compact : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} {U : Set E} (a : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ a (cov U g) → (∀ j : Fin g, ∀ P ∈ cov U g, a (P.1, P.2 + Pi.single j 1) = a P) → ∀ K ⊆ U, IsCompact K → ∀ R : ℝ, 0 ≤ R → ∃ M : ℝ, ∀ n : Fin g → ℤ, ∀ b ∈ K, ‖cf (fun z => a (b, z)) n‖ ≤ M * Real.exp (-(2 * π * R) * l1 n) := by
  first | exact @GlobalTheory.TauPeriod.fibreCoeff_decay | exact GlobalTheory.TauPeriod.fibreCoeff_decay | (intros; apply GlobalTheory.TauPeriod.fibreCoeff_decay <;> assumption)
