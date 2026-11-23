import Mathlib
import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.CmpbHessAtAddConst

open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ComplexConjugate
open scoped ComplexOrder

namespace GlobalTheory

theorem cHess_posSemidef_of_levi_nonneg (n : ℕ) (φ : V n → ℝ) (z : V n) (hf : ContDiffAt ℝ 2 φ z)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) :
    (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  classical
  set g : V n → ℂ := fun v => ((φ v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g z).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) z) = wd n j (wdb n k g) z
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) z, h1, comm_wd_wdb g z hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g z) y) =
      leviV n g z (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

end GlobalTheory
