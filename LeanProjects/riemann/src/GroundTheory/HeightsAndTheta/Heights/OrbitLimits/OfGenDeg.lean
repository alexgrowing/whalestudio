import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
import GroundTheory.HeightsAndTheta.Heights.Intersections.ArithVarZero
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.Inter

theorem PFSum.of_genDeg (h : PushforwardArithIntersection.Statement) : ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement := by
  unfold PushforwardArithIntersection.Statement GenDegStatement at h
  intro I hI K _ ι _ K₂ _ ι₂ _ P₂ d G J L L' hP₂ hP hJ hL hLL'
  exact h I hI K ι (K ⊕ K₂) (Sum.elim ι ι₂) Sum.inl inlV P₂ d G J L L' isBlockMap_inl hP₂ hP hJ hL hLL'

theorem PFSum.of_found (hRat : RatR.Statement) (hCyc : ArithmeticIntersectionCycle.Statement) (hInt : ArithmeticIntersectionIntegral.Statement) :
    ReciprocityTheory.ChartRestriction.G.AI.I4.PFSumStatement :=
  PFSum.of_genDeg (PushforwardArithIntersection.proof arithVarZero hRat hCyc hInt)

end GroundTheory.Heights₂.Heights.Targets
