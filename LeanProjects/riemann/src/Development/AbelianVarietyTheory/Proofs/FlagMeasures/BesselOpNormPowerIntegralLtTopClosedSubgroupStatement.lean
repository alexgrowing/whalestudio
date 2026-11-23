import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselOpNormPowerIntegralLtTopClosedSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselOpNormPowerIntegral_lt_top_closedSubgroup : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (A : ℝ), IsClosedSub k r S → IsHaarOn S μ → 2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < A → normInt μ A < ⊤ := by
  first | exact @GlobalTheory.SgGrowth.normInt_lt_top | exact GlobalTheory.SgGrowth.normInt_lt_top | (intros; apply GlobalTheory.SgGrowth.normInt_lt_top <;> assumption)
