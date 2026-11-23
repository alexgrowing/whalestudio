import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitFiniteSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitDegreeRatio
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitCenterZero
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitLocalSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G NumberField

theorem OrbitFiniteSum.proof (hD : OrbitDegreeRatio.Statement) (hL : OrbitLocalSum.Statement)
    (hZ : OrbitCenterZero.Statement) : OrbitFiniteSum.Statement := by
  classical
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, _, hsa, hsW⟩ := id hs
  have ht : evalCone (coordVec x) s ≠ 0 := evalCone_coordVec_ne_zero x s a hsa hsW
  have hsupp2 : (Function.support fun v : FinitePlace (coordField x) ↦
      Real.log (v (evalCone (coordVec x) s))).Finite := by
    refine Set.Finite.subset (FinitePlace.hasFiniteMulSupport ht) fun v hv h ↦ hv ?_
    simp only [h, Real.log_one]
  have hS := ((finite_support_height A x hx).union hsupp2).subset
    (Function.support_sub (fun v : FinitePlace (coordField x) ↦ finiteTerm A v (coordVec x)) _)
  have hsubF : Function.support (fun v : FinitePlace (coordField x) ↦
      finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) ⊆ hS.toFinset := by
    simp
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := by exact_mod_cast Module.finrank_pos
  have hloc : ∀ V, ∑ᶠ v ∈ {v : FinitePlace (coordField x) | orbitCenter x v = V},
      (finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s))) =
      ∑ v ∈ hS.toFinset, if orbitCenter x v = V then
        finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0 := by
    intro V
    rw [finsum_mem_def, finsum_eq_sum_of_support_subset _
      (by rw [Set.support_indicator]; exact Set.inter_subset_right.trans hsubF)]
    exact Finset.sum_congr rfl fun v _ ↦ by simp [Set.indicator_apply]
  have hterm : ∀ V ∈ (Geo.divSupp_finite (orbitIdeal x) s).toFinset,
      (Geo.multAt (orbitIdeal x ⊔ Ideal.span {s}) V : ℝ) *
          ((Geo.geoNum (ι := blockIdx n) 0 V Fin.elim0 : ℝ) * Real.log (Geo.charOf V)) =
        (∑ v ∈ hS.toFinset, if orbitCenter x v = V then
          finiteTerm A v (coordVec x) - Real.log (v (evalCone (coordVec x) s)) else 0) *
          (Module.finrank ℚ (ratioField x) / Module.finrank ℚ (coordField x) : ℝ) := fun V hV ↦ by
    have h := hL ι n A x s hx hs V ((Geo.divSupp_finite _ _).mem_toFinset.mp hV)
    rw [hloc V] at h
    rw [mul_div_assoc', eq_div_iff hK.ne', mul_comm _ (Module.finrank ℚ (ratioField x) : ℝ), ← h,
      mul_comm]
  rw [finsum_mem_eq_finite_toFinset_sum _ (Geo.divSupp_finite _ _), Finset.sum_congr rfl hterm,
    ← Finset.sum_mul, Finset.sum_comm]
  simp_rw [Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun v _ ↦ by
      split_ifs with h
      · rfl
      · exact (hZ ι n A x s hx hs v fun h' ↦ h ((Geo.divSupp_finite _ _).mem_toFinset.mpr h')).symm,
    ← finsum_eq_sum_of_support_subset _ hsubF, hD ι n x hx]
  ring

end GroundTheory.Heights₂.Heights
