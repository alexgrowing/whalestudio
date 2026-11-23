import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HasFlagDepthAtLeastOfFreeEntriesVanish
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFlagDepthAtLeast_of_free_entries_vanish : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (d : ℕ), x ∈ Nset k r → (∀ β : Bk r, degB r β < d → cM k r β (Matrix.of.symm x) = 0) → Dep k r d (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.dep_of_free_coords | exact GlobalTheory.SnMass.VolN.dep_of_free_coords | (intros; apply GlobalTheory.SnMass.VolN.dep_of_free_coords <;> assumption)
