import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralUnitCongruenceSubgroupRelIndexNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableZterm
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.LatEnt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralUnitCongruenceSubgroup_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → (congr (radN E N)).relIndex (congr (fun _ => 1)) ≠ 0 := by
  first | exact @GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | exact GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero | (intros; apply GlobalTheory.CMVal.LatEnt.relIndex_congr_radN_ne_zero <;> assumption)
