import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CutOutSubgroupTangentSecondOrderHilbertSchmidt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cutOut_subgroup_tangent_second_order_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε S E → ∀ g ∈ S, nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by
  first | exact @GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | exact GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq | (intros; apply GlobalTheory.IwConstApprox.nrm_sub_proj_le_sq <;> assumption)
