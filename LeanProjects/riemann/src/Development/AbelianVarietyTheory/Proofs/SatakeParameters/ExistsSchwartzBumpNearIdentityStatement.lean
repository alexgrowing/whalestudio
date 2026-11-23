import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSchwartzBumpNearIdentity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GodementJacquet MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_bump_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (S : Set (GL (Fin r) k)), IsOpen S → (1 : GL (Fin r) k) ∈ S →
    ∃ Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ, Φ ∈ SB (Matrix (Fin (r + t)) (Fin r) k) ∧
      Φ (eMat k r t) = 1 ∧ (∀ x, Φ x = 0 ∨ Φ x = 1) ∧
      ∀ g : GL (Fin r) k, Φ (eMat k r t * g.val) ≠ 0 → g ∈ S := by
  first | exact @GlobalTheory.GodementJacquet.TestNearE.exists_test | exact GlobalTheory.GodementJacquet.TestNearE.exists_test | (intros; apply GlobalTheory.GodementJacquet.TestNearE.exists_test <;> assumption)
