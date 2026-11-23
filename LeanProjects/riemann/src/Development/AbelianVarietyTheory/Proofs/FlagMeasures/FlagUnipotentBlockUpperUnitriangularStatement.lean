import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagUnipotentBlockUpperUnitriangular
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagUnipotent_block_upper_unitriangular : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), x ∈ Nset k r → Dep k r 1 (x - 1) := by
  first | exact @GlobalTheory.SnMass.VolN.DepOne.dep_one | exact GlobalTheory.SnMass.VolN.DepOne.dep_one | (intros; apply GlobalTheory.SnMass.VolN.DepOne.dep_one <;> assumption)
