import Formalism.WindowSums.Statement
import Formalism.WindowSums.AnnihilatorPolynomials.DistinctTerms

noncomputable section

namespace Formalism.WindowSums

open PowerSeries

theorem pow_mem_ideal_of_le : PowMemIdealOfLe := by
  intro O _ ℓ hℓ ε u y B c hc
  have hℓpos : 0 < ℓ := hℓ.out.pos
  unfold p1 IdLQ
  rw [add_comm, add_pow]
  refine Ideal.sum_mem _ (fun i hi => ?_)
  have hiy : i ≤ y := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hB : B ≤ ℓ * i
  · obtain ⟨k, hk⟩ : ∃ k, ℓ * i = B + k := ⟨ℓ * i - B, by omega⟩
    have : (u * X ^ ℓ) ^ i * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)
        = (u ^ i * X ^ k * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)) * X ^ B := by
      rw [mul_pow, ← pow_mul, hk, pow_add]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · push Not at hB
    have hlt : (i : ℝ) < (B : ℝ) / (ℓ : ℝ) := by
      rw [lt_div_iff₀ (by exact_mod_cast hℓpos)]
      exact_mod_cast (by linarith [hB] : i * ℓ < B)
    have hcy : c ≤ y - i := by
      have : (c : ℝ) < ((y - i + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_sub hiy, Nat.cast_one]; linarith
      have : c < y - i + 1 := by exact_mod_cast this
      omega
    obtain ⟨k, hk⟩ : ∃ k, y - i = c + k := ⟨y - i - c, by omega⟩
    have : (u * X ^ ℓ) ^ i * (C (ℓ : O) * ε) ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)
        = ((u * X ^ ℓ) ^ i * C (ℓ : O) ^ k * ε ^ (y - i) * ((y.choose i : ℕ) : PowerSeries O)) *
          C ((ℓ : O) ^ c) := by
      rw [mul_pow (C (ℓ : O)), map_pow]
      conv_lhs => rw [show C (ℓ : O) ^ (y - i) = C (ℓ : O) ^ c * C (ℓ : O) ^ k by rw [hk, pow_add]]
      ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

end Formalism.WindowSums
