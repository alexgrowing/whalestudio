import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumLeftRightInvarianceNormaliser
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_sum_left_right_invariance_normaliser : GlobalTheory.SatakeWeyl.CellInv := by
  first | exact @GlobalTheory.SatakeWeyl.cellInv_holds | exact GlobalTheory.SatakeWeyl.cellInv_holds | (intros; apply GlobalTheory.SatakeWeyl.cellInv_holds <;> assumption)
