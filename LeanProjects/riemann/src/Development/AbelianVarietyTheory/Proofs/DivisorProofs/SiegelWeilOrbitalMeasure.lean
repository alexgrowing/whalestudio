import Mathlib
open NumberField

namespace GlobalTheory

theorem padicAlgCl_norm_ratCast (q : ℕ) [Fact q.Prime] (c : ℚ) :
    ‖(c : PadicAlgCl q)‖ = ‖((c : ℚ) : ℚ_[q])‖ := by
  rw [← PadicAlgCl.norm_extends q (c : ℚ_[q]), map_ratCast]

theorem norm_conj_le_one_of_bounded_coords :
    ∀ (M : Type) [CommRing M] [Algebra ℚ M] (q : ℕ) [Fact q.Prime] (ι : Type) [Fintype ι]
      (f : M →ₗ[ℚ] (ι → ℚ)), Function.Injective f → ∀ (a : M) (B : ℝ),
      (∀ (k : ℕ) (i : ι), ‖((f (a ^ k) i : ℚ) : ℚ_[q])‖ ≤ B) →
      ∀ τ : M →+* PadicAlgCl q, ‖τ a‖ ≤ 1 := by
  intro M _ _ q _ ι _ f hf a B hB τ
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f (LinearMap.ker_eq_bot.mpr hf)
  have hgf : ∀ m, g (f m) = m := fun m => by
    simpa using LinearMap.congr_fun hg m
  have hsmul : ∀ (c : ℚ) (m : M), τ (c • m) = (c : PadicAlgCl q) * τ m := by
    intro c m
    rw [Algebra.smul_def, map_mul]
    congr 1
    exact eq_ratCast (τ.comp (algebraMap ℚ M)) c
  set C : ℝ := ∑ i, ‖τ (g (Pi.single i 1))‖ with hC
  have hbound : ∀ k : ℕ, ‖τ a‖ ^ k ≤ B * C := by
    intro k
    rw [← norm_pow, ← map_pow, ← hgf (a ^ k)]
    have hv : f (a ^ k) = ∑ i, f (a ^ k) i • (Pi.single i 1 : ι → ℚ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    rw [hv, map_sum, map_sum, hC, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, hsmul, norm_mul, padicAlgCl_norm_ratCast]
    exact mul_le_mul_of_nonneg_right (hB k i) (norm_nonneg _)
  by_contra h
  push_neg at h
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (B * C) h
  exact (lt_irrefl _ ((hbound k).trans_lt hk))

end GlobalTheory
