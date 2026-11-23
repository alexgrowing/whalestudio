import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightDerivativeSmoothOnIndefiniteUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightDerivative_smooth_on_indefinite_unitary_group : ∀ (n : ℕ) (H X : Matrix (Fin n) (Fin n) ℂ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (f : Matrix (Fin n) (Fin n) ℂ → E), Xᴴ * H + H * X = 0 → SmoothOnH H f → ContinuousOn f {g | inUH H g} ∧ SmoothOnH H (rdM X f) ∧ ∀ g, inUH H g → HasDerivAt (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) (rdM X f g) 0 := by
  first | exact @GlobalTheory.rdM_smoothOnH | exact GlobalTheory.rdM_smoothOnH | (intros; apply GlobalTheory.rdM_smoothOnH <;> assumption)
