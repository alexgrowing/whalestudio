import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.GraphChartEventuallyEqSheet
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsLocalBranches
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

theorem LocalOrder.unfolding_form_of_matrix (hB : BranchesToGoodPosition.Statement)
    (h : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement) :
    GroundTheory.Heights₂.Heights.LocalOrder.Statement := by
  intro n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  obtain ⟨q, π, U, V, ρ, hg⟩ := hB n d J W u p m γ ord hJ hdim hu hW hp hcov hsl hdisj hord
  exact h n d J W u q π U V ρ _ ⟨hJ, hdim⟩ hu hW hg

theorem LocalOrder.unfolding_matrix_of_form (hG : GoodPositionToBranches.Statement)
    (h : GroundTheory.Heights₂.Heights.LocalOrder.Statement) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement := by
  intro n e J W u p π U V ρ N hJ hu hW hg
  obtain ⟨q, m, γ, ord, hq, hcov, hsl, hdisj, hord, hsum⟩ :=
    hG n e J W u p π U V ρ N hJ hu hW hg
  rw [← hsum]
  exact h n e J W u q m γ ord hJ.isPrime hJ.dim hu hW hq hcov hsl hdisj hord

theorem LocalOrder.equiv_of (hB : BranchesToGoodPosition.Statement)
    (hG : GoodPositionToBranches.Statement) :
    GroundTheory.Heights₂.Heights.LocalOrder.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.LocalOrder.Statement :=
  ⟨LocalOrder.unfolding_matrix_of_form hG, LocalOrder.unfolding_form_of_matrix hB⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
