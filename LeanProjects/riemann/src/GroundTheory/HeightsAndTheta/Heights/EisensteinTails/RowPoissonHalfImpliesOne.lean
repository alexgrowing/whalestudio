import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.Statements
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.ExistsIntOfIsIntegralThree
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.FourierTailEqEisRest
import GroundTheory.HeightsAndTheta.Heights.EisensteinTails.PRowPoisson
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum

theorem RowPoisson.rowPoisson_half_implies_one :
    GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.RowPoisson.Statement →
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum.RowPoisson.Statement := by
  intro h τ s hs m hm
  have h' := h τ m hm s (by linarith)
  simpa [rowSum_eq, freqIntegral_eq, GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.expTwoPiI,
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum.expTwoPiI] using h'

theorem RowPoisson.equiv :
    GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.RowPoisson.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum.RowPoisson.Statement :=
  ⟨RowPoisson.rowPoisson_half_implies_one,
    fun _ => GroundTheory.Heights₂.Heights.LeavesOrthogonalSum.RowPoisson.proof⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum
