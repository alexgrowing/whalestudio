import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

theorem UpperTheory.Reformulated.B.Gc4.conj_embedding_rt :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
    [inst_2 : NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ),
    (starRingEnd ℂ : ℂ → ℂ) ((τ : E → ℂ) (↑H.rt : E)) =
      -(τ : E → ℂ)
          (↑H.rt :
            E) := by
  intro E _ _ _ H τ
  have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
    simpa using congrArg (algebraMap (NumberField.RingOfIntegers E) E) H.rt_sq
  have h2 : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, h1, map_neg, map_natCast]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  generalize τ (H.rt : E) = z at h2 ⊢
  have hre : z.re * z.re - z.im * z.im = -(H.d : ℝ) := by simpa [sq] using congrArg Complex.re h2
  have him : z.re * z.im + z.im * z.re = 0 := by simpa [sq] using congrArg Complex.im h2
  have hz : z.im ≠ 0 := fun h => by rw [h] at hre; nlinarith [mul_self_nonneg z.re]
  have h0 : z.re = 0 := mul_right_cancel₀ hz (by linarith)
  apply Complex.ext <;> simp [h0]
