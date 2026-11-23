import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory

theorem mem_R_of_adic_limit (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K]
    [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧)
    (hs : ∀ n, s n ∈ R O K l k) (hf : ∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n)
    (ht : Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0)) : f ∈ R O K l k := by
  rw [mem_R]
  have hr : ∀ m : ℕ, 0 ≤ rad l k ^ m := fun m => pow_nonneg (rad_nonneg l k) m
  have hc : ∀ m, coeff m f = coeff m (s m) := fun m => by
    have := X_pow_dvd_iff.1 (hf m) m (Nat.lt_succ_self m)
    rwa [map_sub, sub_eq_zero] at this
  rw [Metric.tendsto_atTop] at ht ⊢
  intro ε hε
  obtain ⟨j, hj⟩ := ht ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (mem_R.1 (hs j)) ε hε
  refine ⟨max j N, fun m hm => ?_⟩
  have key : ∀ t, j ≤ t → ‖coeff m (s t)‖ * rad l k ^ m < ε := by
    intro t h
    induction t, h using Nat.le_induction with
    | base =>
      have := hN m (le_of_max_le_right hm)
      rw [Real.dist_eq, sub_zero] at this
      exact (le_abs_self _).trans_lt this
    | succ t h ih =>
      have h1 := hj t h
      rw [Real.dist_eq, sub_zero] at h1
      have h2 : ‖coeff m (s (t + 1) - s t)‖ * rad l k ^ m < ε :=
        (le_normR (O := O) (sub_mem (hs (t + 1)) (hs t)) m).trans_lt ((le_abs_self _).trans_lt h1)
      have h3 : coeff m (s (t + 1)) = coeff m (s t) + coeff m (s (t + 1) - s t) := by
        rw [map_sub]; ring
      rw [h3]
      refine (mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hr m)).trans_lt ?_
      rw [max_mul_of_nonneg _ _ (hr m)]
      exact max_lt ih h2
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hr m)), hc]
  exact key m (le_of_max_le_left hm)

end GlobalTheory
