import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
open GlobalTheory.PRep GlobalTheory.SmGL Matrix

noncomputable section
namespace GlobalTheory.DetProdNonzero

theorem nontrivial_and_hasFiniteLength : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ), Nontrivial (IndSp (two (stdSum (rfl : u + v = u + v))) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)) ∧ HasFiniteLength (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) := by
  intro k _ _ _ _ hBZ χ₁ χ₂ h₁ h₂ u v
  have s₁ : IsSmooth (detRep (Fin u) χ₁) := (isSmooth_ofChar_iff _).2 h₁.detChar
  have s₂ : IsSmooth (detRep (Fin v) χ₂) := (isSmooth_ofChar_iff _).2 h₂.detChar
  have hc : Continuous (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom :=
    (continuous_apply false).prodMk (continuous_apply true)
  refine ⟨?_, ?_⟩
  · obtain ⟨f, hf, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (two (stdSum (rfl : u + v = u + v)))
      ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)
      (isSmooth_comp (isSmooth_extTensor s₁ s₂) _ hc) ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
    refine ⟨⟨f, 0, fun h => ?_⟩⟩
    have h1 : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) = 0 := by rw [← hf, h]; rfl
    have := congrArg (TensorProduct.lid ℂ ℂ) h1
    simp at this
  · exact GlobalTheory.ProdLength.prod₂_hasFiniteLength hBZ k u v ℂ ℂ _ _
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _))
      (hasFiniteLength_of_isIrreducible (isIrreducible_ofChar _)) s₁ s₂

example : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → ∀ (u v : ℕ), Nontrivial (IndSp (two (stdSum (rfl : u + v = u + v))) ((extTensor (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)).comp (leviTwo k (Fin u) (Fin v)).symm.toMonoidHom)) ∧ HasFiniteLength (prod₂ (detRep (Fin u) χ₁) (detRep (Fin v) χ₂)) := nontrivial_and_hasFiniteLength

end GlobalTheory.DetProdNonzero
end
