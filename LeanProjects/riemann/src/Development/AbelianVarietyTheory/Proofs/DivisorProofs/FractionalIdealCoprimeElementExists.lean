import Mathlib
open NumberField
open scoped nonZeroDivisors

namespace GlobalTheory

theorem exists_mem_spanSingleton_mul_inv_add_eq_one {F : Type} [Field F] [NumberField F]
    (Y N : FractionalIdeal (𝓞 F)⁰ F) (hY : Y ≠ 0) (hN : N ≠ 0) (hN1 : N ≤ 1) :
    ∃ β ∈ Y, FractionalIdeal.spanSingleton (𝓞 F)⁰ β * Y⁻¹ + N = 1 := by
  obtain ⟨N', rfl⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hN1
  obtain ⟨a, Y', ha, rfl⟩ := FractionalIdeal.exists_eq_spanSingleton_mul Y
  have hA : algebraMap (𝓞 F) F a ≠ 0 := by
    intro h; exact ha ((IsFractionRing.to_map_eq_zero_iff).mp h)
  have hAi : (algebraMap (𝓞 F) F a)⁻¹ ≠ 0 := inv_ne_zero hA
  have hS : FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a)⁻¹ ≠ 0 :=
    (FractionalIdeal.spanSingleton_ne_zero_iff).mpr hAi
  have hY' : Y' ≠ ⊥ := by
    rintro rfl; apply hY; simp
  have hN' : N' ≠ ⊥ := by
    rintro rfl; apply hN; simp
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_sup_span_eq (I := Y' * N') (J := Y')
    Ideal.mul_le_left (mul_ne_zero hY' hN')
  have key : (Y' : FractionalIdeal (𝓞 F)⁰ F) * N' +
      FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F r) = Y' := by
    rw [← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_sup, hr]
  have hY'0 : (Y' : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hY'
  have hrY : r ∈ Y' := by
    rw [← hr]; exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self r)
  refine ⟨(algebraMap (𝓞 F) F a)⁻¹ * algebraMap (𝓞 F) F r, ?_, ?_⟩
  · exact FractionalIdeal.mem_singleton_mul.mpr
      ⟨algebraMap (𝓞 F) F r, (FractionalIdeal.mem_coeIdeal _).mpr ⟨r, hrY, rfl⟩, rfl⟩
  · rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, mul_inv, mul_mul_mul_comm,
      mul_comm (FractionalIdeal.spanSingleton (𝓞 F)⁰ (algebraMap (𝓞 F) F a)⁻¹),
      inv_mul_cancel₀ hS, one_mul]
    have h2 := congrArg (· * (Y' : FractionalIdeal (𝓞 F)⁰ F)⁻¹) key
    simp only [add_mul, mul_inv_cancel₀ hY'0] at h2
    rw [mul_comm (Y' : FractionalIdeal (𝓞 F)⁰ F) _, mul_assoc, mul_inv_cancel₀ hY'0, mul_one] at h2
    rw [add_comm]; exact h2

end GlobalTheory
