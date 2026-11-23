import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitArchSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightOrbitConjSum
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PHeightRecR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G

variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem eval_smul_of_isMultiHomog (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by
  have key : ∀ f : MvPolynomial (Coord n) ℤ,
      eval c (Geo.mConeMap (ι := blockIdx n) z f) = eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => simp [Geo.mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf =>
      rw [map_mul, map_mul, map_mul, hf]
      simp [Geo.mConeMap, mul_comm]
  classical
  rw [← key, mConeMap_of_isMultiHomog z s a hs, eval_map]
  simp [map_prod, mul_comm]

theorem OrbitArchSum.proof (hA : PtsIntegralPoints.Statement) (hB : OrbitConjSum.Statement) :
    OrbitArchSum.Statement := by
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
  rw [Geo.arInt, e0, hA ι (blockIdx n) _ _ hfin hinv]
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

end GroundTheory.Heights₂.Heights
