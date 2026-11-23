import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem ProperSymmCycle.proof (h1 : ProperSymm.Statement) (h2 : SupportCycleSection.Statement) :
    ProperSymmCycle.Statement := by
  intro n Z u u' hprime hu hu' hadm W'' hW''
  obtain ⟨W, hW, hW''W⟩ := (h2 n Z u').2 W'' hW''
  have hadmW : IsAdmissible (divCycle W u) u' := fun W' hW' =>
    hadm W' ((h2 n Z u).1 W hW hW')
  exact h1 n W u u' (hprime W hW) (hu W hW) (hu' W hW) hadmW W'' hW''W

end GroundTheory.Heights₂.Heights
