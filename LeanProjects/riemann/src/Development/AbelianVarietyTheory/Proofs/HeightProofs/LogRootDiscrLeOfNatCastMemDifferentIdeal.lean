import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory

theorem log_rootDiscr_le_of_natCast_mem_differentIdeal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (N : ℕ), 0 < N → (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) → Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤ Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K + Real.log N := by
  intro K L _ _ _ _ _ N hN hmem
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have h3 : Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) = N ^ Module.finrank ℚ L := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (pow_pos hN _) h2
  have h5 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L := by
    rw [h1]; exact Nat.mul_le_mul_right _ h4
  have hL : (0 : ℝ) < |((discr L : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero L)
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h6 : |((discr L : ℤ) : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ L * |((discr K : ℤ) : ℝ)| ^ Module.finrank K L := by
    have : (((discr L).natAbs : ℕ) : ℝ) ≤ ((N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) := by
      exact_mod_cast h5
    simpa [Nat.cast_natAbs] using this
  have h7 := Real.log_le_log hL h6
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h7
  have h8 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hk : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hl : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h9 : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by exact_mod_cast h8
  rw [div_le_iff₀ hl]
  refine h7.trans (le_of_eq ?_)
  rw [← h9]
  field_simp
  ring

end GlobalTheory
