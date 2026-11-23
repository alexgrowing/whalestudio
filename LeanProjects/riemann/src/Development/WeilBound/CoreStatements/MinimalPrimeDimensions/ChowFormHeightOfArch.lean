import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.IsClosedOfCoheight
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.DescEval
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.SumNormSqUnitary
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FormHeightOneEq
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.StCharts
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.ChowDegreeSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Assembly

namespace ChowFormHeightComparison₂.CF

open GroundTheory.Heights₂.Heights in
theorem chowFormHeight_of_arch (hA : StArch) (hM : MahlerSection.Statement) (hE : GlobalTheory.Published.ArExists) :
    PositivityTheory.UnitarySelfGeneration.ChowFormHeight :=
  glue (stMain_of (stVert stPts stPull stDiv) hA
    (ChowHeightRecursion.of_leaves ChowFormSectionVertical.full hM ChowFormBaseChange.full BaseChangeAvoid.full)
    ChowFormSection.full ChowHeightMul.full ProjPrimeHasPoint.full) stModel stForm hE

end ChowFormHeightComparison₂.CF
