import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightAssembly
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitDivVertical
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitFiniteSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitArchSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPtsIntegralPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

theorem OrbitArchSum.of_conjSum (hB : OrbitConjSum.Statement) : OrbitArchSum.Statement := by
  intro ι _ _ _ n A x s hx hs
  obtain ⟨a, ha, hsa, -⟩ := hs
  have hinv : ∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) →
      Geo.logNorm A.toGeo s (fun p ↦ c p.1 * z p) = Geo.logNorm A.toGeo s z := by
    intro c z hc _
    rw [Geo.logNorm, Geo.logNorm, A.toGeo.smul c z hc, eval_smul_of_isMultiHomog s a hsa c z,
      norm_mul, norm_prod]
    simp only [ha, zpow_natCast, norm_pow]
    rw [mul_div_mul_left _ _ (Finset.prod_ne_zero_iff.mpr fun k _ ↦
      pow_ne_zero _ (norm_ne_zero_iff.mpr (hc k)))]
  have hfin := (Nat.card_pos_iff.mp (OrbitDegree.full ι n x hx)).2
  have e0 : (fun j z ↦ Real.log (((Fin.elim0 : Fin 0 → Geo.HermLine (blockIdx n)) j).h z)) =
      (Fin.elim0 : Fin 0 → (Coord n → ℂ) → ℝ) := funext fun j ↦ j.elim0
  have hB' := hB ι n x _ hx hinv
  rw [Geo.arInt, e0, PtsIntegralPoints.homogProof ι (blockIdx n) _ _
    (OrbitCurve.isMultiHomogIdeal_orbitIdeal x) hfin hinv]
  have hterm : ∀ σ : coordField x →+* ℂ,
      Geo.logNorm A.toGeo s (fun p ↦ σ (coordVec x p.1 p.2)) =
        Real.log (‖evalCone (fun k i ↦ σ (coordVec x k i)) s‖ /
          A.metric (fun k i ↦ σ (coordVec x k i))) := by
    intro σ
    rw [Geo.logNorm, ← eval_map_flatCone]
    rw [A.toGeo_h_of_blockNonzero (w := fun p ↦ σ (coordVec x p.1 p.2)) (blockNonzero_sigma hx σ)]
    rfl
  simp only [hterm] at hB'
  have hK : (0 : ℝ) < Module.finrank ℚ (coordField x) := Nat.cast_pos.mpr Module.finrank_pos
  rw [div_mul_eq_mul_div, hB', mul_div_cancel_left₀ _ hK.ne']

theorem HeightAsIntersection.of_orbit_parts (hD : OrbitDegreeRatio.Statement)
    (hL : OrbitLocalSum.Statement) (hZ : OrbitCenterZero.Statement)
    (hB : OrbitConjSum.Statement) : HeightAsIntersection.Statement :=
  HeightAsIntersection.of_parts OrbitDivVertical.proof (OrbitFiniteSum.proof hD hL hZ)
    (OrbitArchSum.of_conjSum hB)

end GroundTheory.Heights₂.Heights
