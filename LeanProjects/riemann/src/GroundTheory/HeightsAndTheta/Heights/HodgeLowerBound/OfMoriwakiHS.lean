import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

theorem ArithKleiman.of_moriwakiHS (hM : MoriwakiHSStatement) (hB : BirationalModelExists.Statement) :
    ArithKleiman.Statement := by
  intro K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW
  obtain ⟨Ω, _, y, hyP, hbir⟩ := hB K ι P (D + 1) hP
  subst hyP
  have hgen : NefOnGeneric (mCoordIdeal y) A :=
    NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP0 hsemi
  have hlim := hM K ι Ω y D A P0 II hII hP hbir hP0 hsemi hconj hnef hgen hW
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ ?_
  · exact Real.log_natCast_nonneg _
  · positivity

theorem Z1.proof (hM : MoriwakiHSStatement) (hB : BirationalModelExists.Statement) : SuccessiveMinimaLowerBound :=
  G5.proof' (ArithKleiman.of_moriwakiHS hM hB) CurvePointsFinite.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
