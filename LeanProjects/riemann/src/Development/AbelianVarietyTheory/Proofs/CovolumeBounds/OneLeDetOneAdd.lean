import Mathlib

open scoped ComplexOrder

namespace GlobalTheory.OneLeDetOneAdd

theorem one_le_det_one_add {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {D : Matrix n n 𝕜} (hD : D.PosSemidef) : (1 : 𝕜) ≤ (1 + D).det := by
  have hA : (1 + D).IsHermitian := Matrix.isHermitian_one.add hD.1
  have hμ : ∀ i, 1 ≤ hA.eigenvalues i := by
    intro i
    have hv1 : RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm]
      simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hA.eigenvectorBasis.orthonormal.1 i, algebraMap.coe_one, one_pow, RCLike.one_re]
    have h := hA.eigenvalues_eq i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, map_add, hv1] at h
    have h0 := hD.re_dotProduct_nonneg ⇑(hA.eigenvectorBasis i)
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i, hA.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hA.eigenvalues i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hμ i)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  calc (1 : 𝕜) = ((1 : ℝ) : 𝕜) := by simp
    _ ≤ _ := RCLike.ofReal_le_ofReal.mpr hprod

end GlobalTheory.OneLeDetOneAdd
