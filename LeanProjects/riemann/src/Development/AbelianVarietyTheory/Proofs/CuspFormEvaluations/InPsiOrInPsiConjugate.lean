import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.LetAct

set_option autoImplicit false

namespace GlobalTheory.CMTypeOrConjugate

open NumberField

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have h1 : (starRingEnd ℂ z) ^ 2 = z ^ 2 := by
    rw [← map_pow, hz, map_neg, map_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
  · exfalso
    obtain ⟨x, rfl⟩ := Complex.conj_eq_iff_real.mp h
    have h2 : x ^ 2 = -(d : ℝ) := by exact_mod_cast hz
    have h3 : (0 : ℝ) < d := by exact_mod_cast hd
    nlinarith [sq_nonneg x]
  · exact h

theorem inPsi_or_inPsi_conjugate {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : E →+* ℂ) :
    Formalism.L2.Pj.InPsi H τ ∨ Formalism.L2.Pj.InPsi H (ComplexEmbedding.conjugate τ) := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast] at h
    exact h
  have hz : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    rw [← map_pow, hE, map_neg, map_natCast]
  unfold Formalism.L2.Pj.InPsi
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hz.trans H.sqrt_neg_disc_sq.symm) with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, conj_eq_neg_of_sq H.d_prime.pos hz, h, neg_neg]

end GlobalTheory.CMTypeOrConjugate
