import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzCompactSupportDense
import Mathlib
open MeasureTheory Filter Topology
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_compact_support_dense : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (f : SchwartzMap V ℂ),
    f ∈ closure {g : SchwartzMap V ℂ | HasCompactSupport (g : V → ℂ)} := by
  first | exact @GlobalTheory.schwartz_mem_closure_hasCompactSupport | exact GlobalTheory.schwartz_mem_closure_hasCompactSupport | (intros; apply GlobalTheory.schwartz_mem_closure_hasCompactSupport <;> assumption)
