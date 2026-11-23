import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.DifferentiableAtChart

namespace ReciprocityTheory.L2DbarEstimates.Y

open Filter Topology Set ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open scoped ContDiff

noncomputable section

theorem fc_clm_decomp (n : ℕ) (D : V n →L[ℝ] ℂ) (u : V n) :
    D u = ∑ a, ((D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2 * u a +
      (D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2 * (starRingEnd ℂ) (u a)) := by
  have hu : u = ∑ a, ((u a).re • bas n a + (u a).im • (Complex.I • bas n a)) := by
    ext b
    simp [bas, EuclideanSpace.single_apply, Finset.sum_add_distrib, Complex.real_smul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
  conv_lhs => rw [hu]
  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]
  have h1 : u a = ((u a).re : ℂ) + ((u a).im : ℂ) * Complex.I := (Complex.re_add_im _).symm
  have h2 : (starRingEnd ℂ) (u a) = ((u a).re : ℂ) - ((u a).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  linear_combination (-(D (bas n a) - Complex.I * D (Complex.I • bas n a)) / 2) * h1 +
    (-(D (bas n a) + Complex.I * D (Complex.I • bas n a)) / 2) * h2 +
    (((u a).im : ℂ) * D (Complex.I • bas n a)) * Complex.I_mul_I

theorem fc_wdb_holo (n : ℕ) (p : V n → ℂ) (v : V n) (hp : DifferentiableAt ℂ p v) (j : Fin n) :
    wdb n j p v = 0 := by
  unfold wdb
  rw [hp.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars', map_smul, smul_eq_mul]
  linear_combination (fderiv ℂ p v (bas n j) / 2) * Complex.I_mul_I

theorem fc_wd_sum (n : ℕ) (j : Fin n) {ι : Type*} (s : Finset ι) (f : ι → V n → ℂ) (v : V n)
    (hf : ∀ a ∈ s, DifferentiableAt ℝ (f a) v) :
    wd n j (fun y => ∑ a ∈ s, f a y) v = ∑ a ∈ s, wd n j (f a) v := by
  unfold wd
  have e : (fun y => ∑ a ∈ s, f a y) = ∑ a ∈ s, f a := by
    funext y
    simp
  rw [e, fderiv_sum hf]
  simp only [ContinuousLinearMap.sum_apply]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]

theorem fc_leviV_congr (n : ℕ) (g₁ g₂ : V n → ℂ) (v : V n) (h : g₁ =ᶠ[𝓝 v] g₂)
    (ξ : Fin n → ℂ) : leviV n g₁ v ξ = leviV n g₂ v ξ := by
  unfold leviV
  have hk : ∀ k, wdb n k g₁ =ᶠ[𝓝 v] wdb n k g₂ := fun k =>
    h.eventuallyEq_nhds.mono fun y hy => by
      unfold wdb
      rw [hy.fderiv_eq (𝕜 := ℝ)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  unfold wd
  rw [(hk k).fderiv_eq (𝕜 := ℝ)]

end

end ReciprocityTheory.L2DbarEstimates.Y
