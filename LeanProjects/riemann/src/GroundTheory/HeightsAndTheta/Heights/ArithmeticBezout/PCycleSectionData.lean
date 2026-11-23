import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem CycleSectionData.proof (h1 : CycleSectionChow.Statement) (h2 : DivCyclePrime.Statement)
    (h3 : SpecFirstHomog.Statement) (h4 : SupportCycleSection.Statement) :
    CycleSectionData.Statement := by
  intro n e δ Z f u hZ hu
  refine ⟨?_, ?_, ?_⟩
  · intro W' hW'
    obtain ⟨W, hW, hW'W⟩ := (h4 n Z u).2 W' hW'
    exact h2 n W u (hZ.prime W hW) W' hW'W
  · exact h1 n (e + 1) Z f u hZ.prime hZ.chow hu
  · exact h3 n (e + 1) δ f u hZ.homog

end GroundTheory.Heights₂.Heights
