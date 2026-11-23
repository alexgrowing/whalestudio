import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCellSumLeviReductionOfSteps
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryCellSumLeviReduction_of_steps : GlobalTheory.SatakeWeyl.RankOne → GlobalTheory.SatakeWeyl.EmbExists → GlobalTheory.SatakeWeyl.EmbMem → GlobalTheory.SatakeWeyl.EmbTorus → GlobalTheory.SatakeWeyl.LeviRad → GlobalTheory.SatakeWeyl.UnipSplit → GlobalTheory.SatakeWeyl.Contract → GlobalTheory.SatakeWeyl.TorusConj → GlobalTheory.SatakeWeyl.LeviStep := by
  first | exact @GlobalTheory.SatakeWeyl.leviStep_of_steps | exact GlobalTheory.SatakeWeyl.leviStep_of_steps | (intros; apply GlobalTheory.SatakeWeyl.leviStep_of_steps <;> assumption)
