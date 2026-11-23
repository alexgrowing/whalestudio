import Mathlib

open scoped TensorProduct

namespace PositivityTheory.KB.PrimeModuloFree

theorem exists_nsmul_eq_zero_of_tmul {A : Type*} [AddCommGroup A] [Module ℤ A] (a : A)
    (h : (1 : ℝ) ⊗ₜ[ℤ] a = 0) : ∃ r : ℕ, r ≠ 0 ∧ r • a = 0 := by
  by_contra hne
  push Not at hne
  let f : ℤ →ₗ[ℤ] A := LinearMap.toSpanSingleton ℤ A a
  have hf1 : f 1 = a := by
    simp only [f, LinearMap.toSpanSingleton_apply]
    first | exact one_smul ℤ a | exact one_zsmul a | exact (int_smul_eq_zsmul _ _ _).trans (one_zsmul a)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro n hn
    by_contra h0
    apply hne n.natAbs (Int.natAbs_ne_zero.mpr h0)
    have e : n.natAbs • a = f (n.natAbs : ℤ) := by
      rw [← nsmul_one (n.natAbs : ℕ), map_nsmul, hf1]
    rw [e, Int.natCast_natAbs]
    rcases abs_choice n with h1 | h1
    · rw [h1, hn]
    · rw [h1, map_neg, hn, neg_zero]
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) f hf
  have h3 : (LinearMap.lTensor ℝ f) ((1 : ℝ) ⊗ₜ[ℤ] (1 : ℤ)) = 0 := by
    rw [LinearMap.lTensor_tmul, hf1]
    exact h
  have h4 : (1 : ℝ) ⊗ₜ[ℤ] (1 : ℤ) = 0 := h2 (by rw [h3, map_zero])
  have h5 := congrArg (TensorProduct.rid ℤ ℝ) h4
  simp at h5

end PositivityTheory.KB.PrimeModuloFree
