import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitLemmaUnitaryGroupOddResidueOfLie
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_odd_residue_of_lie : UnitLemmaLie → UnitLemmaGroup := by
  first | exact @GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | exact GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie | (intros; apply GlobalTheory.UnitLemma.Orbit.unitLemmaGroup_of_lie <;> assumption)
