import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsCompactOpenUnitsSubgroupContinuousSqrt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibOfZero
open MeasureTheory Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_open_units_subgroup_continuous_sqrt : ∀ (K : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K], (2 : K) ≠ 0 → ∃ (U : Set K) (s : K → K), GlobalTheory.QuadFibre.IsSqrtOn U s := by
  first | exact @GlobalTheory.QuadFibre.exists_isSqrtOn | exact GlobalTheory.QuadFibre.exists_isSqrtOn | (intros; apply GlobalTheory.QuadFibre.exists_isSqrtOn <;> assumption)
