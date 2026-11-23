import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.DivisorIdealBotUniformiser
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem NoCommonComponentCase.proof (h₁ : LeftExpansion.Statement.{u}) (h₂ : RightExpansion.Statement.{u})
    (h₃ : LocalCoefficient.Statement.{u}) (h₄ : IntNumVanish.Statement.{u}) :
    NoCommonComponentCase.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hH hno L
  unfold cutIdentity
  rw [h₁ O ϖ hϖ K ι P d hP b f g hD.1 c s hs hsP hno L,
    h₂ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno L]
  unfold cycEval
  refine finsum_congr fun U => ?_
  beta_reduce
  by_cases hU : U.IsPrime ∧ IsMultiHomogIdeal U ∧ IsRelevant U ∧ (C ϖ : MRing ι O) ∈ U ∧
      ¬ ((d + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι O ⧸ U)
  ·
    obtain ⟨hUp, hUm, -, hϖU, hdim⟩ := hU
    have hv : vNum U L = 0 := by
      refine h₄ _ K ι d (specialIdeal U) (SpecialIdealCorresp.proof O ϖ hϖ K ι ⊥ U hUp hϖU).1
        (SpecialIdealMultiHomog.proof O K ι U hUm) (Or.inr ?_) L
      rw [SpecialQuotDim.proof O ϖ hϖ K ι U hϖU]
      exact lt_of_not_ge hdim
    rw [hv, mul_zero, mul_zero]
  ·
    have e := h₃ O ϖ hϖ K ι P d hP b f g hD c s hs hsP hH hno U fun hp hm hr hϖU => by
      by_contra h
      exact hU ⟨hp, hm, hr, hϖU, h⟩
    unfold cycEval at e
    rw [e]

end GroundTheory.Heights₂.Heights.NumbersDVR
