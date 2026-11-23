import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionIsMulAction
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_action_is_mul_action : ∀ g : ℕ, (∀ P ∈ cov (siegel g) g, actU 1 P = P) ∧ (∀ γ γ' : Sp g, ∀ P ∈ cov (siegel g) g, actU (γ * γ') P = actU γ (actU γ' P)) := by
  first | exact @GlobalTheory.SympUnivGroup.group_action | exact GlobalTheory.SympUnivGroup.group_action | (intros; apply GlobalTheory.SympUnivGroup.group_action <;> assumption)
