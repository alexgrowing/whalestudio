import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovariantRepresentation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CountableConjSub

noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.CovariantRepresentation

theorem shiftCore : ShiftCore := by
  intro G _ _ _ _ _ _ μ _ _ R Γ _ V _ _ f Ω h ν _ hΓR hK hn hσ hne hcon hfin hleft hinv hconj hf hΩ hfi
  by_cases hV : CompleteSpace V
  · exact Formalism.L2.SG.MeasureShiftInvariance.shift_general μ R Γ f Ω h ν hΓR hK hn hσ hne hcon hfin hleft hinv hconj
      hf hΩ hfi
  · rw [integral_of_not_completeSpace hV, integral_of_not_completeSpace hV]

end Formalism.L2.SG.CovariantRepresentation
