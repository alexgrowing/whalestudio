import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterZero
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterLe
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterMemIff
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterDivSupp
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

theorem OrbitCenterZero.proof (hLe : OrbitCenterLe.Statement)
    (hIff : OrbitCenterMemIff.Statement) (hDiv : OrbitCenterDivSupp.Statement) :
    OrbitCenterZero.Statement := by
  intro ι _ _ _ n A x s hx ⟨a, ha, hs, hsW⟩ v hv
  have hsc : s ∉ orbitCenter x v := fun h ↦ hv (hDiv ι n x s a hx hs hsW v h)
  have heq : v (evalCone (coordVec x) s) = ∏ k, (⨆ i, v (coordVec x k i)) ^ a k :=
    le_antisymm (hLe ι n x v s a hs) (not_lt.mp (mt (hIff ι n x hx v s a hs).mpr hsc))
  have hne : v (evalCone (coordVec x) s) ≠ 0 :=
    (FinitePlace.pos_iff.mpr (evalCone_coordVec_ne_zero x s a hs hsW)).ne'
  rw [heq] at hne ⊢
  rw [Real.log_prod (fun k _ ↦ Finset.prod_ne_zero_iff.mp hne k (Finset.mem_univ k)),
    finiteTerm, sub_eq_zero]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Real.log_pow, show (A.deg k : ℝ) = (a k : ℝ) by exact_mod_cast ha k]

end GroundTheory.Heights₂.Heights
