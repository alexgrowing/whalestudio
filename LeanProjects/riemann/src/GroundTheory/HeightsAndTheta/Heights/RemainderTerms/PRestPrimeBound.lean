import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

theorem RestPrimeBound.proof (h₁ : RestPrimeBoundOfFactor.Statement)
    (h₂ : SameFactorBound.Statement) (h₃ : OtherFactorBound.Statement) :
    RestPrimeBound.Statement := by
  intro f r a c B₀ hf hr ha hB
  obtain ⟨_, hQex, hsame⟩ := h₂ f r a c hf hr ha
  obtain ⟨_, _, hother⟩ := h₃ f r a c hf hr ha
  refine ⟨hQex, ?_⟩
  intro Q hQ s e he p hp hBp
  refine h₁ f r a c B₀ hf hr ha hB Q ?_ s e he p hp hBp
  intro k hk2 hkN τ τ'
  by_cases h : τ' = τ
  · subst h
    exact hsame Q hQ k hk2 hkN τ'
  · exact (hother Q hQ k hk2 hkN τ τ' h).2

end RestTerms

end GroundTheory.Heights₂.Heights
