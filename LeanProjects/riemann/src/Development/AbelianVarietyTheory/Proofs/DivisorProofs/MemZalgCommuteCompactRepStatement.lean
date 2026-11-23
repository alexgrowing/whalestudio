import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_zalg_commute_compactRep : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (k : GlobalTheory.CuspRep.Kinf E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.cptRep E a k = GlobalTheory.CuspRep.cptRep E a k * z := by
  first | exact @GlobalTheory.ZalgCpt.zalg_comm_cptRep | exact GlobalTheory.ZalgCpt.zalg_comm_cptRep | (intros; apply GlobalTheory.ZalgCpt.zalg_comm_cptRep <;> assumption)
