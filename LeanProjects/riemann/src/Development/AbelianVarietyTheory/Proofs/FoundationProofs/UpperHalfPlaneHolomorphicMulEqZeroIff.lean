import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_mul_eq_zero_dom : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  intro f g hf hg hfg
  have hF := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hG := (UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ({z : ℂ | 0 < z.im}).Nonempty := ⟨Complex.I, by simp⟩
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hF hG (fun z _ => by simp [Function.comp_apply, hfg]) hU with h | h
  · left
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this
  · right
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
