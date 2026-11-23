import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupStructureOfHyp
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_structure_of_published_inputs : GlobalTheory.Published.RaynaudExtension → GlobalTheory.Published.GrothendieckOrthogonality → GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.GroupBplus.GroupSt := by
  first | exact @GlobalTheory.GroupBplus.groupSt | exact GlobalTheory.GroupBplus.groupSt | (intros; apply GlobalTheory.GroupBplus.groupSt <;> assumption)
