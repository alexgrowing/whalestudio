import Mathlib
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Statements
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomNbhd
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsDescendHom
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsGenericPullInj
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.StatementsSpreadHomSections
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Model

open CategoryTheory AlgebraicGeometry

lemma opensRange_homOfLE_invOpen {X : Scheme.{0}} (f : X ⟶ SpecZ) {a k : ℤ}
    (h : invOpen f k ≤ invOpen f a) :
    (X.homOfLE h).opensRange = invOpen ((invOpen f a).ι ≫ f) k := by
  rw [Scheme.opensRange_homOfLE]
  rfl

theorem SpreadHomNbhd.proof (h₁ : DescendHom.Statement) (h₂ : GenericPullInj.Statement)
    (h₃ : SpreadHomSections.Statement) : SpreadHomNbhd.Statement := by
  intro X f _ _ a ha F G hF hG φ
  obtain ⟨m₁, hm₁, H₁⟩ := h₂ X f a ha G hG
  obtain ⟨m₂, hm₂, H₂⟩ := h₃ X f a ha F G hF hG φ
  have hn : 0 < m₁ * m₂ := Nat.mul_pos hm₁ hm₂
  have hWa : invOpen f ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ)) ≤ invOpen f a := invOpen_mul_le_left f a _
  have hW := range_baseChangeMap_subset f ℚ ((a : ℤ) * ((m₁ * m₂ : ℕ) : ℤ))
    (isUnit_intCast_rat _ (by positivity))
  have hR := opensRange_homOfLE_invOpen f hWa
  refine ⟨_, hWa, hW, h₁ _ _ _ (X.homOfLE hWa) (toOpen f ℚ _ hW) _
    (toOpen_homOfLE f ℚ _ hW (isUnit_intCast_rat a (by exact_mod_cast ha.ne')) hWa) F G φ
    (fun V hV => H₁ _ hn (dvd_mul_right _ _) V (hR ▸ hV))
    (fun V hV => H₂ _ hn (dvd_mul_left _ _) V (hR ▸ hV))⟩

end GroundTheory.Heights₂.Heights.Model
