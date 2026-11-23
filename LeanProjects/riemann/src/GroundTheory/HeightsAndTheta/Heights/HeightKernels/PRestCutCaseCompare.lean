import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsRest
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem RestCutCaseCompare.proof (h₁ : RestTerms.SameFactorBound.Statement)
    (h₂ : RestCutRestHom.Statement) (h₃ : RestCutStairNonzero.Statement)
    (h₄ : RestCutCompare.Statement) (h₅ : RestCutCompareReal.Statement) :
    RestCutCaseCompare.Statement := by
  intro f j k r a cs e hf hr ha hN hJ I hI
  have hD : flagDim f j k = RestTerms.topDegree f (r + a) := by
    simp only [flagDim, RestTerms.topDegree, hN]
  have hHh := (h₂ f r a cs).1
  have hJ0 : RestTerms.fibreDegree f r a cs ≠ 0 := (h₁ f r a cs hf hr ha).1
  have hst : RestTerms.flagIntegral f (r + a) (restStair f (r + a)) ≠ 0 := h₃ f (r + a) _ hHh hJ0
  refine ⟨restCompareConst f j k (r + a) e I, ?_, ?_⟩
  · exact h₅ f j k (r + a) e I _ (flagDim f j k) fun H' hH' => h₄ f j k (r + a) e I hI hst H' hH'
  · rw [← hJ]
    exact h₄ f j k (r + a) e I hI hst _ (hD ▸ hHh)

end GroundTheory.Heights₂.Heights
