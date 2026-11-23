import Mathlib

open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2

theorem mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

theorem coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by
  intro J _ b hb h0 t
  have hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hb
  have hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0 := by
    ext y
    choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)
    have hy : y = fun j => (x j : UnitAddCircle) := funext fun j => (hx j).symm
    have h1 := ((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq
    simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1
    rw [← h1, hy]
    simp only [mFourier_coe_eq_exp]
    simpa using h0 x
  have hsum := hs.hasSum
  rw [hz] at hsum
  exact coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t

end GlobalTheory
