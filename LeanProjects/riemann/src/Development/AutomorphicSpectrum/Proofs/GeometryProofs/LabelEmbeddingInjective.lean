import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem labels_all_once : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Geo.Tor.Level H)
    (c : Coeff l), Function.Injective (labelEmb (H := H) c) ∧
      Nat.card (CMType H ⊕ CMType H) = Module.finrank ℚ E := by
  intro E _ _ _ H l c
  classical
  have hre : H.rt0.re = 0 := by
    have h : (H.rt0 * H.rt0).re = (-(H.d : ℂ)).re := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h
    have h' : (H.rt0 * H.rt0).im = (-(H.d : ℂ)).im := by rw [← pow_two, H.sqrt_neg_disc_sq]
    rw [Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h'
    have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
    have h1 : H.rt0.re * H.rt0.im = 0 := by linarith
    have h2 : H.rt0.re * H.rt0.re * (H.rt0.re * H.rt0.re + H.d) = 0 := by nlinarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact mul_self_eq_zero.1 h3
    · nlinarith [mul_self_nonneg H.rt0.re]
  have hconj0 : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hne : H.rt0 ≠ 0 := by
    intro h0
    have h := H.sqrt_neg_disc_sq
    rw [h0, zero_pow two_ne_zero, eq_comm, neg_eq_zero, Nat.cast_eq_zero] at h
    exact H.d_prime.ne_zero h
  have hneg : -H.rt0 ≠ H.rt0 := by
    intro h
    apply hne
    have h2 : (2 : ℂ) * H.rt0 = 0 := by linear_combination -h
    rcases mul_eq_zero.1 h2 with h3 | h3
    · norm_num at h3
    · exact h3
  have hsq : ∀ τ : E →+* ℂ, (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    intro τ
    have e1 := congrArg (fun x : 𝓞 E => τ (algebraMap (𝓞 E) E x)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at e1
    rw [H.sqrt_neg_disc_sq]
    exact e1
  have hpm : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 :=
    fun τ => sq_eq_sq_iff_eq_or_eq_neg.1 (hsq τ)
  have hcc : ∀ τ : E →+* ℂ, τ (IsCMField.complexConj E (H.rt : E)) = -τ (H.rt : E) := by
    intro τ
    rw [IsCMField.complexEmbedding_complexConj]
    rcases hpm τ with h | h
    · rw [h, hconj0]
    · rw [h, map_neg, hconj0]
  refine ⟨?_, ?_⟩
  · have k1 : ∀ (τ : CMType H) (x : 𝓞 E), ((labelEmb c (Sum.inl τ) x : ℂ)) = τ.1 (x : E) :=
      fun _ _ => rfl
    have k2 : ∀ (τ : CMType H) (x : 𝓞 E),
        ((labelEmb c (Sum.inr τ) x : ℂ)) = τ.1 ((H.bar x : 𝓞 E) : E) := fun _ _ => rfl
    have ext' : ∀ τ τ' : E →+* ℂ, (∀ x : 𝓞 E, τ (x : E) = τ' (x : E)) → τ = τ' := by
      intro τ τ' h
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext h)
    rintro (τ | τ) (τ' | τ') h
    · refine congrArg Sum.inl (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h x)
      rwa [k1, k1] at e
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k1, k2, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e.symm
    · exfalso
      have e := congrArg Subtype.val (RingHom.congr_fun h H.rt)
      rw [k2, k1, H.bar_eq, hcc, τ.2, τ'.2] at e
      exact hneg e
    · refine congrArg Sum.inr (Subtype.ext (ext' _ _ fun x => ?_))
      have e := congrArg Subtype.val (RingHom.congr_fun h (H.bar.symm x))
      rwa [k2, k2, RingEquiv.apply_symm_apply] at e
  · let e : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} :=
      { toFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq, τ.2, hconj0]
            exact hneg⟩
        invFun := fun τ => ⟨ComplexEmbedding.conjugate τ.1, by
            rw [ComplexEmbedding.conjugate_coe_eq]
            rcases hpm τ.1 with h | h
            · exact absurd h τ.2
            · rw [h, map_neg, hconj0, neg_neg]⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq])
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by
            simp [ComplexEmbedding.conjugate_coe_eq]) }
    have hc : Nat.card (CMType H ⊕ CMType H) = Nat.card (E →+* ℂ) :=
      Nat.card_congr ((Equiv.sumCongr (Equiv.refl _) e).trans (Equiv.sumCompl _))
    rw [hc, Nat.card_eq_fintype_card, NumberField.Embeddings.card E ℂ]

end GlobalTheory.CompanionTheory.Ar
