import Mathlib
open NumberField

namespace GlobalTheory

theorem isTorsionFree_ringOfIntegers_of_isTorsionFree_int (E : Type) [Field E] [NumberField E]
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree (𝓞 E) N := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun c x hcx => ?_)
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have halg : IsAlgebraic ℤ c := (Algebra.IsIntegral.isIntegral (R := ℤ) c).isAlgebraic
    obtain ⟨m, hm, d, hd⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
    have h1 : m • x = 0 := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E)]
      have : ((m : ℤ) : 𝓞 E) = d * c := by
        rw [mul_comm, ← hd]; simp
      rw [this, mul_smul, hcx, smul_zero]
    exact (smul_eq_zero.mp h1).resolve_left hm

end GlobalTheory
