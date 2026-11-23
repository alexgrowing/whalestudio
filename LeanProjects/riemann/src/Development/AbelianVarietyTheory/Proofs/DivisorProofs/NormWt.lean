import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds

noncomputable section

open NumberField

namespace GlobalTheory.HeckeStrip

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

def wt (φ : I → K →+* ℂ) (n : I → ℤ) (α : K) : ℂ :=
  ∏ i, (φ i α / ((‖φ i α‖ : ℝ) : ℂ)) ^ (-n i)

def pval (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (J : Ideal (𝓞 K)) [J.IsPrincipal] : ℂ :=
  F (Submodule.IsPrincipal.generator J) * wt φ n ((Submodule.IsPrincipal.generator J : 𝓞 K) : K)

def pSeries (F : 𝓞 K → ℂ) (φ : I → K →+* ℂ) (n : I → ℤ) (s : ℂ) : ℂ :=
  ∑' J : {J : Ideal (𝓞 K) // J ≠ ⊥ ∧ J.IsPrincipal},
    (haveI := J.2.2; pval F φ n J.1) * ((Ideal.absNorm J.1 : ℕ) : ℂ) ^ (-s)

theorem wt_mul (φ : I → K →+* ℂ) (n : I → ℤ) (a b : K) : wt φ n (a * b) = wt φ n a * wt φ n b := by
  unfold wt
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, norm_mul, Complex.ofReal_mul, mul_div_mul_comm, mul_zpow]

theorem norm_wt (φ : I → K →+* ℂ) (n : I → ℤ) {a : K} (ha : a ≠ 0) : ‖wt φ n a‖ = 1 := by
  unfold wt
  rw [norm_prod]
  refine Finset.prod_eq_one fun i _ => ?_
  have h : φ i a ≠ 0 := (map_ne_zero _).2 ha
  rw [norm_zpow, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self (norm_ne_zero_iff.2 h), one_zpow]

end GlobalTheory.HeckeStrip
