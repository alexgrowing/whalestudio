import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBridge
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem VocabDivCycle.proof : VocabDivCycle.Statement := by
  intro R _ _ K _ ι _ P s W
  classical
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℕ) = if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
      ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.divCycle, Finsupp.ofSupportFinite_coe]
  rw [e, divCycle]
  by_cases h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s
  · have h' : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W := h
    have hW : W.IsPrime := h'.1.1.1
    rw [if_pos h, dif_pos h', ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos hW]
    rfl
  · have h' : ¬ (W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W) := h
    rw [if_neg h, dif_neg h']
    rfl

end

end GroundTheory.Heights₂.Heights.NumbersDVR
