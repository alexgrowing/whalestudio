import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

theorem SpreadIso.proof (h₁ : SpreadHom.Statement) (h₂ : SpreadHomInj.Statement) :
    SpreadIso.Statement := by
  intro X f _ _ a ha F G hF hG α
  obtain ⟨m₁, hm₁, H₁⟩ := h₁ X f a ha F G hF hG α.hom
  obtain ⟨m₂, hm₂, H₂⟩ := h₁ X f a ha G F hG hF α.inv
  obtain ⟨m₃, hm₃, I₃⟩ := h₂ X f a ha F F hF hF
  obtain ⟨m₄, hm₄, I₄⟩ := h₂ X f a ha G G hG hG
  obtain ⟨n, hn_def⟩ : ∃ n, n = m₁ * m₂ * m₃ * m₄ := ⟨_, rfl⟩
  have hn : 0 < n := by rw [hn_def]; positivity
  obtain ⟨ψ₁, e₁⟩ := H₁ n hn (Dvd.intro (m₂ * m₃ * m₄) (by rw [hn_def]; ring))
  obtain ⟨ψ₂, e₂⟩ := H₂ n hn (Dvd.intro (m₁ * m₃ * m₄) (by rw [hn_def]; ring))
  have k₁ : ψ₁ ≫ ψ₂ = 𝟙 _ := I₃ n hn (Dvd.intro (m₁ * m₂ * m₄) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₁, e₂, Iso.hom_inv_id])
  have k₂ : ψ₂ ≫ ψ₁ = 𝟙 _ := I₄ n hn (Dvd.intro (m₁ * m₂ * m₃) (by rw [hn_def]; ring)) _ _ (by
    rw [pullbackHomAlong_comp, pullbackHomAlong_id, e₂, e₁, Iso.inv_hom_id])
  refine ⟨n, hn, ⟨ψ₁, ψ₂, k₁, k₂⟩, Iso.ext ?_⟩
  rw [pullbackIsoAlong_hom]
  exact e₁

end GroundTheory.Heights₂.Heights.Model
