import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsFibreFamilyEqAtContinuityPoint
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFibreFamily_eq_at_continuity_point : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) (f : V → ℝ) (O U U' : Set V) (B B' : Set ℝ) (fib fib' : ℝ → Measure V) (β : ℝ), Measurable f → IsOpen O → O ⊆ U → O ⊆ U' → f ⁻¹' {β} ⊆ O → IsOpen B → IsOpen B' → β ∈ B → β ∈ B' → IsFibreFamily μ f id U (volume : Measure ℝ) B fib → IsFibreFamily μ f id U' (volume : Measure ℝ) B' fib' → fib β = fib' β := by
  first | exact @GlobalTheory.IsFibreFamily_eq_at | exact GlobalTheory.IsFibreFamily_eq_at | (intros; apply GlobalTheory.IsFibreFamily_eq_at <;> assumption)
