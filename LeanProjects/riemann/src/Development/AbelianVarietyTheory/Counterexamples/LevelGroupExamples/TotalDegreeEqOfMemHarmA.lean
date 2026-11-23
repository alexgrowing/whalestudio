import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaRuleCheck
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem inPsi_conjugate_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]; simp
  have h2 : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h := H.sqrt_neg_disc_sq
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have h0 : H.rt0 ≠ -H.rt0 := by
    intro h
    have : H.rt0 = 0 := by linear_combination h / 2
    have h' := H.sqrt_neg_disc_sq
    rw [this] at h'
    have : (H.d : ℂ) = 0 := by linear_combination h'
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  simp only [InPsi, ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h]
  · rw [h2]; simp [h0.symm]
  · rw [map_neg, h2]; simp [h0.symm]

end GlobalTheory.ThetaRuleCheck
