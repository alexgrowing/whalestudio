import Mathlib

namespace GroundTheory.Global

open NumberField IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

theorem norm_natCast_adicCompletion_eq_one {v : HeightOneSpectrum (𝓞 K)} {n : ℕ}
    (hv : (n : 𝓞 K) ∉ v.asIdeal) : ‖(n : v.adicCompletion K)‖ = 1 := by
  have h := (FinitePlace.norm_eq_one_iff_notMem (K := K) (v := v) (n : 𝓞 K)).2 hv
  rwa [map_natCast, map_natCast] at h

theorem finprod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 K), ‖(n : v.adicCompletion K)‖) *
      (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h := FinitePlace.prod_eq_inv_abs_norm hn'
  simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
    FinitePlace.equivHeightOneSpectrum_symm_apply, map_natCast] at h
  rw [h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  have hpos : (0 : ℝ) < (n : ℝ) ^ Module.finrank ℚ K := by positivity
  push_cast
  rw [abs_of_pos hpos, inv_mul_cancel₀ hpos.ne']

theorem prod_norm_natCast_adicCompletion_mul {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) * (n : ℝ) ^ Module.finrank ℚ K = 1 := by
  rw [← finprod_eq_prod_of_mulSupport_subset]
  · exact finprod_norm_natCast_adicCompletion_mul hn
  · intro v hv
    by_contra h
    exact hv (norm_natCast_adicCompletion_eq_one fun h' ↦ h (hS v h'))

theorem prod_norm_natCast_infinitePlaceCompletion_pow_mult (n : ℕ) :
    ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = (n : ℝ) ^ Module.finrank ℚ K := by
  have h := InfinitePlace.prod_eq_abs_norm (n : K)
  have hw : ∀ w : InfinitePlace K, ‖(n : w.Completion)‖ = w (n : K) := fun w ↦ by
    rw [← map_natCast (algebraMap K w.Completion) n]
    exact InfinitePlace.Completion.norm_coe (K := K) (v := w) _
  simp_rw [hw, h, ← map_natCast (algebraMap ℚ K) n, Algebra.norm_algebraMap]
  push_cast
  exact abs_of_nonneg (by positivity)

theorem prod_norm_natCast_mul_prod_infinitePlace {n : ℕ} (hn : n ≠ 0)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (hS : ∀ v, (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (∏ v ∈ S, ‖(n : v.adicCompletion K)‖) *
      ∏ w : InfinitePlace K, ‖(n : w.Completion)‖ ^ w.mult = 1 := by
  rw [prod_norm_natCast_infinitePlaceCompletion_pow_mult]
  exact prod_norm_natCast_adicCompletion_mul hn S hS

end GroundTheory.Global
