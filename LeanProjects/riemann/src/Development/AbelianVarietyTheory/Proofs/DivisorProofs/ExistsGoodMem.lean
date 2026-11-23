import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.FerrandPush

theorem exists_good_mem : ∀ {Y₀ Y₁ Y₂ : Scheme.{0}} (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) [IsClosedImmersion i₁] [Surjective i₁] [IsClosedImmersion i₂] [Surjective i₂] (x : Y₀), ∃ U ∈ GlobalTheory.FerrandPush.good i₁ i₂, x ∈ U := by
  intro Y₀ Y₁ Y₂ i₁ i₂ _ _ _ _ x
  obtain ⟨V₁, hV₁, hx₁, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y₁.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (i₁ x))
  obtain ⟨V₂, hV₂, hx₂, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y₂.isBasis_affineOpens (TopologicalSpace.Opens.mem_top (i₂ x))
  have hV₁' : IsAffineOpen V₁ := hV₁
  have hV₂' : IsAffineOpen V₂ := hV₂
  have hW₁ : IsAffineOpen (i₁ ⁻¹ᵁ V₁) := hV₁'.preimage i₁
  have hW₂ : IsAffineOpen (i₂ ⁻¹ᵁ V₂) := hV₂'.preimage i₂
  obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hW₁ hW₂ x ⟨hx₁, hx₂⟩
  obtain ⟨f', rfl⟩ := i₁.app_surjective V₁ hV₁' f
  obtain ⟨g', rfl⟩ := i₂.app_surjective V₂ hV₂' g
  refine ⟨Y₀.basicOpen ((i₁.app V₁).hom f'), ⟨hW₁.basicOpen _, ?_, ?_⟩, hxf⟩
  · rw [← Scheme.preimage_basicOpen, upOpen_preimage]
    exact hV₁'.basicOpen f'
  · rw [e, ← Scheme.preimage_basicOpen, upOpen_preimage]
    exact hV₂'.basicOpen g'

end GlobalTheory.FerrandPush
