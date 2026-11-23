import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConj
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AgreeOfAdjoin
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjEqNegOfSq

noncomputable section

open NumberField

namespace UpperTheory.Gal.CertificateRingHomMap

private theorem agree_of_adjoin {E : Type} [Field E] [NumberField E] (φ ψ : E →+* ℂ) {a b : E}
    (h : φ a = ψ a) (hb : b ∈ IntermediateField.adjoin ℚ {a}) : φ b = ψ b :=
  _root_.UpperTheory.Reformulated.B.Qk58.agree_of_adjoin φ ψ h hb

private theorem conj_eq_neg_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) z = -z :=
  _root_.UpperTheory.Reformulated.B.Qk60.conj_eq_neg_of_sq hd hz

theorem pEpsIff_of : EpsIff := by
  intro E _ _ _ d x ω hd hx hω hx' τ φ
  have hτ : (τ x) ^ 2 = -(d : ℂ) := by
    rw [← map_pow, hx, map_neg, map_natCast]
  have hc : ComplexEmbedding.conjugate τ x = -τ x := by
    rw [ComplexEmbedding.conjugate_coe_eq]
    exact conj_eq_neg_of_sq hd hτ
  constructor
  · intro h
    have h' : φ ω = ComplexEmbedding.conjugate τ ω := by
      rw [ComplexEmbedding.conjugate_coe_eq]
      exact h
    rw [agree_of_adjoin φ _ h' hx', hc]
  · intro h
    have h' : φ x = ComplexEmbedding.conjugate τ x := by rw [h, hc]
    rw [agree_of_adjoin φ _ h' hω, ComplexEmbedding.conjugate_coe_eq]

end UpperTheory.Gal.CertificateRingHomMap

end
