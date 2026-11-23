import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadStep
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadGlue
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.PSpreadBundle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite

theorem SpreadStep.proof (h₁ : SpreadIsoLoc.Statement) (h₂ : SpreadGlue.Statement) :
    SpreadStep.Statement := by
  intro X f _ _ p E W₁ W₂ ⟨E₁, hE₁, ⟨α₁⟩⟩ ⟨E₂, hE₂, ⟨α₂⟩⟩
  obtain ⟨m, -, hmp, ψ, hψ⟩ := h₁ X f p (W₁ ⊓ W₂) _ _
    (hE₁.pullback_of_isOpenImmersion _) (hE₂.pullback_of_isOpenImmersion _)
    (overlapIso f (ZLoc p) E α₁ α₂)
  have hV : Set.range (baseChangeMap f (ZLoc p)) ⊆ Set.range (invOpen f m).ι :=
    range_baseChangeMap_subset f _ m (isUnit_intCast_zLoc p m (by exact_mod_cast hmp))
  refine ⟨(W₁ ⊔ W₂) ⊓ invOpen f m, ?_, h₂ X f (ZLoc p) E W₁ W₂ E₁ E₂ hE₁ hE₂ α₁ α₂ _ hV ψ hψ⟩
  intro y hy
  have hyV : (baseChangeMap f (ZLoc p)).base y ∈ invOpen f m := by
    have := hV ⟨y, rfl⟩
    rwa [Scheme.Opens.range_ι] at this
  refine ⟨?_, hyV⟩
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr hy

end GroundTheory.Heights₂.Heights.Model
