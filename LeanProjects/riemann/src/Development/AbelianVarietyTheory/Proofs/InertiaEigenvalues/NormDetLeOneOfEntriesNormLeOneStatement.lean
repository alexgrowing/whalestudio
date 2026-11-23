import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormDetLeOneOfEntriesNormLeOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_det_le_one_of_entries_norm_le_one : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E), (∀ i j, ‖x i j‖ ≤ 1) → ‖x.det‖ ≤ 1 := by
  first | exact @GlobalTheory.norm_det_le_one_of_entries_le_one | exact GlobalTheory.norm_det_le_one_of_entries_le_one | (intros; apply GlobalTheory.norm_det_le_one_of_entries_le_one <;> assumption)
