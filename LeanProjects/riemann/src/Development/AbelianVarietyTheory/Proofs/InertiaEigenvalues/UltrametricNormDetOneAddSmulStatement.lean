import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UltrametricNormDetOneAddSmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommOfBezout
open GlobalTheory.UnitDiscAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_norm_det_one_add_smul : ∀ (E : Type) [NontriviallyNormedField E] [IsUltrametricDist E] (n : ℕ) (x : Matrix (Fin n) (Fin n) E) (ϖ : E), ‖ϖ‖ < 1 → (∀ i j, ‖x i j‖ ≤ 1) → ‖(1 + ϖ • x).det‖ = 1 := by
  first | exact @GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | exact GlobalTheory.UnitDiscAlg.norm_det_one_add_smul | (intros; apply GlobalTheory.UnitDiscAlg.norm_det_one_add_smul <;> assumption)
