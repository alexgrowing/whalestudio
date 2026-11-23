import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem FN.germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  refine ⟨⟨(Filter.Germ.coeRingHom _).comp (Pi.ringHom fun z => Pi.evalRingHom (fun _ : ℍ => ℂ) (UpperHalfPlane.ofComplex z)), fun f => rfl⟩, fun f => ?_, ?_, ?_, fun τ => τ.2⟩
  · exact UpperHalfPlane.mdifferentiable_iff
  · intro a b h
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  · intro a
    unfold germ up
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end GlobalTheory
