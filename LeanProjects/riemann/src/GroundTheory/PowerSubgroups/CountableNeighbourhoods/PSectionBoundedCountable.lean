import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

namespace GroundTheory.Variant₂.N1

noncomputable def coeffNorm {K : Type} {ι : K → Type} (G : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) : ℝ :=
  ∑ m ∈ MvPolynomial.support G, ‖(Int.castRingHom ℂ) (MvPolynomial.coeff m G)‖

theorem norm_eval_le_of_forall_norm_le {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {z : (k : K) × ι k → ℂ} {c : (k : K) → ι k}
    (hz : ∀ (k : K) (i : ι k), ‖z ⟨k, i⟩‖ ≤ ‖z ⟨k, c k⟩‖)
    {G : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι} {δ : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G δ) :
    ‖(MvPolynomial.eval z) ((MvPolynomial.map (Int.castRingHom ℂ)) G)‖ ≤
      coeffNorm G * ∏ k : K, ‖z ⟨k, c k⟩‖ ^ δ k := by
  rw [MvPolynomial.eval_map, MvPolynomial.eval₂_eq', coeffNorm, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  rw [norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod, Fintype.prod_sigma]
  refine Finset.prod_le_prod (fun k _ => Finset.prod_nonneg fun i _ => norm_nonneg _) fun k _ => ?_
  rw [← hG m hm k, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hz k i) _

end GroundTheory.Variant₂.N1
