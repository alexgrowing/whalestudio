import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinates
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NCoords
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_lie_nilpotent_coordinates : ∀ (k r : ℕ), IsHaarOn (Nset k r) (haarLie (Nset k r) 1) ∧ Set.InjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} ∧ Set.SurjOn (nCoords k r) {x | Matrix.of x ∈ Nset k r} Set.univ ∧ (haarLie (Nset k r) 1).map (nCoords k r) = (2 : ℝ≥0∞) ^ (r * (r - 1) + r * (k + 1)) • volume := by
  first | exact @GlobalTheory.SnMass.NEntry.haarLie_entries | exact GlobalTheory.SnMass.NEntry.haarLie_entries | (intros; apply GlobalTheory.SnMass.NEntry.haarLie_entries <;> assumption)
