import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeChartIntegrable
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeIntegralComponents
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

open ConeIntegralComponents in

theorem ConeChartIntegrable.proof (hEx : ChowFormExists.Statement)
    (hBC : ChowFormBaseChange.Statement) (hInt : ConeFsLogIntegrable.Statement) :
    ConeChartIntegrable.Statement := by
  intro n e h P u hP hu
  classical
  set S := (fundCycle (complexFibreIdeal P)).support with hS
  set μ := Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ) (X := EuclideanSpace ℂ (Fin n)) with hμ
  obtain ⟨g, hg⟩ := exists_chowForm_components hEx hBC hP
  have h0 : IntegrableOn (fun y => fsLog h u (h.pointOf y)) ({0} : Set (EuclideanSpace ℂ (Fin n))) μ := by
    rw [IntegrableOn, Measure.restrict_eq_zero.2 (hausdorffMeasure_zero e)]
    exact integrable_zero_measure
  have hW : IntegrableOn (fun y => fsLog h u (h.pointOf y)) (⋃ W ∈ S, coneBall h W) μ :=
    integrableOn_finset_iUnion.2 fun W hW => hInt n e h W (g W) u (hg W hW).1 (hg W hW).2 (hu W hW)
  exact (h0.union hW).mono_set (coneBall_subset h (complexFibreIdeal_isRadical hP))

end GroundTheory.Heights₂.Heights
