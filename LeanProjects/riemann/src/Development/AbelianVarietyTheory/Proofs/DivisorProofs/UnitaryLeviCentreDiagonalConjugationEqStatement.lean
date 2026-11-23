import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviCentreDiagonalConjugationEq
import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
open Formalism.UG GlobalTheory.SatakeWeyl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_levi_centre_diagonal_conjugation_eq : GlobalTheory.SatakeWeyl.TorusConj := by
  first | exact @GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | exact GlobalTheory.SatakeWeyl.TorusConjProof.torusConj | (intros; apply GlobalTheory.SatakeWeyl.TorusConjProof.torusConj <;> assumption)
