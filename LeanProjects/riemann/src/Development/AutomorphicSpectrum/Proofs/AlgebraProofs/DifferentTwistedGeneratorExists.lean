import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsRealDifferentGeneratorStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.RelDiff

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rt_sq_field (H : Host E) : ((H.rt : E)) ^ 2 = -(H.d : E) := by
  have h := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  rw [map_pow, map_neg, map_natCast] at h
  exact h

theorem rt_ne_zero (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have h1 := rt_sq_field H
  rw [h, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h1
  exact H.d_prime.ne_zero h1

theorem conj_eq_neg_of_sq {z : ℂ} {d : ℝ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero] at hre him
  have h0 : z.re = 0 := by
    rcases mul_eq_zero.mp (show z.re * z.im = 0 by nlinarith) with h | h
    · exact h
    · rw [h] at hre
      nlinarith [sq_nonneg z.re]
  apply Complex.ext <;> simp [h0]

theorem conj_rt (H : Host E) : IsCMField.complexConj E (H.rt : E) = -(H.rt : E) := by
  let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, map_neg]
  apply conj_eq_neg_of_sq (d := (H.d : ℝ)) (by exact_mod_cast H.d_prime.pos)
  rw [← map_pow, rt_sq_field, map_neg, map_natCast]
  simp

theorem exists_local_generator (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ℓ : Nat.Primes) :
    ∃ δ : E, δ ≠ 0 ∧ ∀ j : E →+* ℂ_[ℓ],
      Real.log ‖j δ‖ = logIdeal (j.comp (algebraMap (𝓞 E) E)) (differentIdeal ℤ (𝓞 E)) - Real.log ‖j (H.rt : E)‖ ∧
      Real.log ‖j (IsCMField.complexConj E δ)‖ = Real.log ‖j δ‖ := by
  obtain ⟨δ₀, -, hδ₀, hconj, hlog⟩ := GlobalTheory.T.exists_real_different_generator E H.unram ℓ
  have hrt : (H.rt : E) ≠ 0 := rt_ne_zero H
  have hδ₀E : (δ₀ : E) ≠ 0 := by exact_mod_cast hδ₀
  refine ⟨(δ₀ : E) / (H.rt : E), div_ne_zero hδ₀E hrt, fun j => ⟨?_, ?_⟩⟩
  · rw [map_div₀, norm_div,
      Real.log_div (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hδ₀E))
        (norm_ne_zero_iff.mpr ((map_ne_zero j).mpr hrt)), hlog]
  · rw [map_div₀, hconj, conj_rt H, div_neg, map_neg, norm_neg]

end GlobalTheory.CompanionTheory.Ar.Fl.RelDiff
