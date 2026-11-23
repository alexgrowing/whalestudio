import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureUnipotentTuplesFreeEntryBlocks
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieNilpotentCoordinatesStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_unipotent_tuples_free_entry_blocks : ∀ (ι : Type) [Fintype ι] (k r : ℕ) (DU : UTr r → Set (ι → ℂ)) (DH : Fin r → Set (ι → Fin (k + 1) → ℂ)) (DC : UTr r → Set (ι → ℂ)) (DG : Fin r → Set (ι → ℝ)), (∀ p, MeasurableSet (DU p)) → (∀ a, MeasurableSet (DH a)) → (∀ p, MeasurableSet (DC p)) → (∀ a, MeasurableSet (DG a)) → MeasurableSet {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} ∧ (Measure.pi fun _ : ι => haarLie (Nset k r) 1) {x : ι → Mt k r | (∀ w, Matrix.of (x w) ∈ Nset k r) ∧ ∀ β : Bk r, (fun w => cM k r β (x w)) ∈ blkSet ι k r DU DH DC DG β} = (2 : ℝ≥0∞) ^ (Fintype.card ι * (r * (r - 1) + r * (k + 1))) * ((∏ p, volume (DU p)) * (∏ a, volume (DH a)) * (∏ p, volume (DC p)) * ∏ a, volume (DG a)) := by
  first | exact @GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks | exact GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks | (intros; apply GlobalTheory.SnMass.VolN.BlockMeas.measure_blocks <;> assumption)
