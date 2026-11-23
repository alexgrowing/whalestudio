import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentBlockEntriesMulOfHasFlagDepthAtLeast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotentBlockEntries_mul_of_hasFlagDepthAtLeast : ∀ (k r : ℕ) (g x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), Dep k r d (g - 1) → Dep k r 1 (x - 1) → ∀ β : Bk r, degB r β ≤ d → cM k r β (Matrix.of.symm (g * x)) = cM k r β (Matrix.of.symm x) + cM k r β (Matrix.of.symm g) := by
  first | exact @GlobalTheory.SnMass.VolN.cM_mul_of_dep | exact GlobalTheory.SnMass.VolN.cM_mul_of_dep | (intros; apply GlobalTheory.SnMass.VolN.cM_mul_of_dep <;> assumption)
