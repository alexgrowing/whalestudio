import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CellSumRankOneReflectionSymmetryOfSteps
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cellSumRankOneReflectionSymmetry_of_steps : GlobalTheory.SatakeWeyl.Descent → GlobalTheory.SatakeWeyl.CellInv → GlobalTheory.SatakeWeyl.ChainSum → GlobalTheory.SatakeWeyl.RankOne := by
  first | exact @GlobalTheory.SatakeWeyl.rankOne_of_steps | exact GlobalTheory.SatakeWeyl.rankOne_of_steps | (intros; apply GlobalTheory.SatakeWeyl.rankOne_of_steps <;> assumption)
