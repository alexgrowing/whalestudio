import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HermitianFormNormSqLeReMulRe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_norm_sq_le_re_mul_re_of_posDef : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ v w, Bf w v = starRingEnd ℂ (Bf v w)) → (∀ v, v ≠ 0 → 0 < (Bf v v).re) →
    ∀ v w, ‖Bf v w‖ ^ 2 ≤ (Bf v v).re * (Bf w w).re := by
  first | exact @GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | exact GlobalTheory.hermitianForm_norm_sq_le_re_mul_re | (intros; apply GlobalTheory.hermitianForm_norm_sq_le_re_mul_re <;> assumption)
