import Formalism.LocalRingCardinality.DataHost
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow

namespace Formalism.BasicNotions

open NumberField

variable {R : Ranks}

theorem Host.sqrtMinusD_sq (H : Host R) : H.sqrtMinusD ^ 2 = -(H.d : H.E) := by
  exact H.sqd_sq

theorem Host.conj_sqrtMinusD (H : Host R) : H.conj H.sqrtMinusD = -H.sqrtMinusD := by
  apply H.φ₀.injective
  have h1 : H.φ₀ (H.conj H.sqrtMinusD) = starRingEnd ℂ (H.φ₀ H.sqrtMinusD) := H.conjE_apply H.φ₀ H.sqrtMinusD
  rw [h1, map_neg]
  set z := H.φ₀ H.sqrtMinusD
  have hz : z ^ 2 = -(H.d : ℂ) := by rw [← map_pow, H.sqrtMinusD_sq]; simp
  have hre : z.re = 0 := by
    have h2 := congrArg Complex.im hz
    have h3 := congrArg Complex.re hz
    simp [pow_two] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.hyp.2.1.pos
    rcases mul_eq_zero.mp (show z.re * z.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact h
      · rw [h] at h3; nlinarith [sq_nonneg z.re]
    · norm_num at h
  apply Complex.ext <;> simp [hre]

theorem Host.exists_trace_one (H : Host R) : ∃ c : 𝓞 H.E, (c : H.E) + H.conj c = 1 := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.hyp.2.2.2.1; omega⟩
  set c : H.E := (1 + H.sqrtMinusD) / 2
  have hc : c ^ 2 - c + (m : H.E) = 0 := by
    have e : ((H.d : ℕ) : H.E) + 1 = 4 * (m : H.E) := by exact_mod_cast hm
    have hs := H.sqrtMinusD_sq
    simp only [c]
    linear_combination (1 / 4 : H.E) * hs - (1 / 4 : H.E) * e
  have hint : IsIntegral ℤ c := ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (m : ℤ), by monicity!, by
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_add, hc]⟩
  refine ⟨⟨c, hint⟩, ?_⟩
  show c + H.conj c = 1
  simp only [c, map_div₀, map_add, map_one, H.conj_sqrtMinusD, map_ofNat]
  ring

theorem factTrOne (D : D7) : ∃ c : 𝓞 D.host.E, (c : D.host.E) + D.host.conj c = 1 :=
  D.host.exists_trace_one

end Formalism.BasicNotions
