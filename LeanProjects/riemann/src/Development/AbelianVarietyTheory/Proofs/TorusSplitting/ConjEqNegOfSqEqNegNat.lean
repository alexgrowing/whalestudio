import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth

namespace GlobalTheory.ImaginarySqrtEmbedding

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h0 : z.re = 0 := by
    by_contra hne
    have him0 : z.im = 0 := by
      have h2 : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.mp h2).resolve_left hne
    have hpos : 0 < z.re * z.re := mul_self_pos.mpr hne
    rw [him0] at hre
    linarith
  apply Complex.ext <;> simp [h0]

theorem embedding_sqrt_sq_and_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : E →+* ℂ) :
    τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
        = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) ∧
      starRingEnd ℂ (τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E))
        = -τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  have h1 : τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
      = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at h
    exact h
  exact ⟨h1, conj_eq_neg_of_sq_eq_neg_nat _ _ h1⟩

end GlobalTheory.ImaginarySqrtEmbedding
