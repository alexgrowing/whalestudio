import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV

set_option autoImplicit false

namespace GlobalTheory.ConjugateNegativeSquare

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h0 : z.re = 0 := by
    by_contra hne
    have hi : z.im = 0 := by
      have h2 : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left hne
    rw [hi] at hre
    have hpos : 0 < z.re * z.re := mul_self_pos.2 hne
    linarith
  apply Complex.ext
  · simp [h0]
  · simp

theorem conjugate_rt {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (σ : E →+* ℂ) :
    (ComplexEmbedding.conjugate σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) =
      -(σ : E → ℂ) (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  obtain ⟨d, _, _, rt, hrt, _, _, _, _, _, _, _⟩ := H
  change ComplexEmbedding.conjugate σ (rt : E) = -σ (rt : E)
  rw [ComplexEmbedding.conjugate_coe_eq]
  apply conj_eq_neg_of_sq_eq_neg_nat _ d
  have h1 : (rt : E) ^ 2 = -(d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) hrt
    simpa using this
  rw [← map_pow, h1, map_neg, map_natCast]

end GlobalTheory.ConjugateNegativeSquare
