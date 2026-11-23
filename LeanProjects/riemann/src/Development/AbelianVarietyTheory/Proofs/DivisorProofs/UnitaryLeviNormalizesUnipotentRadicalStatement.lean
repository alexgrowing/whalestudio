import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_normalizes_unipotent_radical : GlobalTheory.SatakeWeyl.LeviRad := by
  first | exact @GlobalTheory.SatakeWeyl.leviRad | exact GlobalTheory.SatakeWeyl.leviRad | (intros; apply GlobalTheory.SatakeWeyl.leviRad <;> assumption)
