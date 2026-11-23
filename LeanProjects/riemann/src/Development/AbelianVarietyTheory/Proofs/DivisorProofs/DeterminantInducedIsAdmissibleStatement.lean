import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeterminantInducedIsAdmissible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantModulus

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinant_induced_isAdmissible : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x x' : ℕ) (α β : kˣ →* ℂˣ),
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.ThK.MidJac.detInd x x' α β) := by
  first | exact @GlobalTheory.ThK.MidJac.isAdmissible_detInd | exact GlobalTheory.ThK.MidJac.isAdmissible_detInd | (intros; apply GlobalTheory.ThK.MidJac.isAdmissible_detInd <;> assumption)
