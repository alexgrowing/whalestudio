import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingTriangularShear
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_add_of_triangular : ∀ (d : ℕ) (deg : Fin d → ℕ) (f : (Fin d → ℝ) → (Fin d → ℝ)), Measurable f → (∀ x y i, (∀ k, deg k < deg i → x k = y k) → f x i = f y i) → MeasurePreserving (fun x => x + f x) (volume : Measure (Fin d → ℝ)) volume := by
  first | exact @GlobalTheory.measurePreserving_triangular_shear | exact GlobalTheory.measurePreserving_triangular_shear | (intros; apply GlobalTheory.measurePreserving_triangular_shear <;> assumption)
