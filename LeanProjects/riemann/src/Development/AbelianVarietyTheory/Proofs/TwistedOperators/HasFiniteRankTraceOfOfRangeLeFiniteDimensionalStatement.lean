import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasFiniteRankTraceOfOfRangeLeFiniteDimensional
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IwahoriDoubleCosets
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFiniteRankTraceOf_of_range_le_finiteDimensional : ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (T : X →ₗ[ℂ] X) (Z : Submodule ℂ X)
    [FiniteDimensional ℂ Z] (hT : LinearMap.range T ≤ Z),
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace T (LinearMap.trace ℂ Z (T.restrict (p := Z) (q := Z)
      fun x _ => hT (LinearMap.mem_range_self T x))) := by
  first | exact @GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | exact GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le | (intros; apply GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le <;> assumption)
