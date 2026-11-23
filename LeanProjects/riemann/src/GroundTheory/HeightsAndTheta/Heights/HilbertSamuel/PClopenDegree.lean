import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClopenComponents
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentsAdditive
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsIntNumComponents
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem ClopenDegree.proof (h₁ : ClopenComponents.Statement) (h₂ : ComponentDegree.Statement)
    (h₃ : ComponentsAdditive.Statement) (h₄ : IntNumComponents.Statement) : ClopenDegree.Statement := by
  intro K _ _ ι _ P e L A hP hL hA hcl
  obtain ⟨S, hS, hAS, hI⟩ := h₁ K ι P e A hP hA hcl
  rw [hI, hAS, h₃ K ι P e L S hP hL hS, h₄ K ι P e _ S hP hS]
  push_cast
  exact Finset.sum_congr rfl fun W hW => h₂ K ι P e L W hP hL (hS W hW)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
