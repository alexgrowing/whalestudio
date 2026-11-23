import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
open NumberField GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_zalg_commute_lie_action : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a) (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a → z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  first | exact @GlobalTheory.CuspRep.Zalg_mul_lie | exact GlobalTheory.CuspRep.Zalg_mul_lie | (intros; apply GlobalTheory.CuspRep.Zalg_mul_lie <;> assumption)
