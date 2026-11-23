import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlTwoPosRatMobiusUpperHalfPlanePropertiesStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem cmp_props :
    (∀ f : ℍ → ℂ, GlobalTheory.FN.cmp 1 f = f) ∧ (∀ (g h : GQ) (f : ℍ → ℂ), GlobalTheory.FN.cmp (g * h) f = GlobalTheory.FN.cmp h (GlobalTheory.FN.cmp g f)) ∧
      (∀ (γ : SL(2, ℤ)) (f : ℍ → ℂ), GlobalTheory.FN.cmp (ofSL γ) f = fun τ => f (γ • τ)) ∧
        ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
  obtain ⟨hH, hmul, hone, hsl, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_upperHalfPlane_properties
  have hup : ∀ (f : ℍ → ℂ) (z : ℂ) (hz : 0 < z.im), up f z = f ⟨z, hz⟩ := by
    intro f z hz
    simp only [up, UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  have hupH : ∀ (f : ℍ → ℂ) (τ : ℍ), up f τ = f τ := by
    intro f τ
    simp only [up, UpperHalfPlane.ofComplex_apply]
  have h4 : ∀ (g : GQ) (f : ℍ → ℂ), ∀ z ∈ Hs, up (GlobalTheory.FN.cmp g f) z = up f (mob g z) := by
    intro g f z hz
    rw [hup _ z hz]
    rfl
  refine ⟨?_, ?_, ?_, h4⟩
  · intro f
    funext τ
    simp only [cmp, hone, hupH]
  · intro g h f
    funext τ
    have hτ : (τ : ℂ) ∈ Hs := τ.im_pos
    show up f (mob (g * h) τ) = up (cmp g f) (mob h τ)
    rw [h4 g f _ (hH h _ hτ), hmul g h _ hτ]
  · intro γ f
    funext τ
    simp only [cmp, hsl, hupH]

end GlobalTheory.FN
