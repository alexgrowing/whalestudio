import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PAnalyticDerivBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartFrameDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartGradient
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagContinuous
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartImagMean
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartLowerHeightsound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartPeriodImPos
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PChartPotentialPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCoordinateBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspCovolume
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspLattice
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspLeadingMinima
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspShortVectors
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PCuspTimeDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PGramPivotProduct
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramDropLast
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramQf
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramSubLast
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramUnimodular
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PInvEntryDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadingCovolume
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadMinorBasic
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadMinorLeading
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramContinuous
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramPsh
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramSubmean
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PMatrixDetDeriv
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodGramPosDef
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodHermValue
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPeriodLatticeCovolume
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotBounds
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotInvDiag
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotLast
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PPivotProductBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PSchurDetBound
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PUnimodularLast
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.HermValueIsLeast
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Period
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LogDetGramContinuous.full : LogDetGramContinuous.Statement := LogDetGramContinuous.proof

theorem LogDetGramSubmean.full : LogDetGramSubmean.Statement :=
  LogDetGramSubmean.proof LogDetGramContinuous.full

theorem InvEntryBound.full : InvEntryBound.Statement := InvEntryBound.proof

theorem InvEntryDeriv.full : InvEntryDeriv.Statement := InvEntryDeriv.proof InvEntryBound.full

theorem LogDetGramDeriv.full : LogDetGramDeriv.Statement :=
  LogDetGramDeriv.proof InvEntryBound.full InvEntryDeriv.full MatrixDetDeriv.proof
    GramEntryDeriv.proof

theorem AnalyticDerivBound.full : AnalyticDerivBound.Statement := AnalyticDerivBound.proof

theorem ChartFrameDeriv.full : ChartFrameDeriv.Statement :=
  ChartFrameDeriv.proof AnalyticDerivBound.full

theorem ChartImagDeriv.full : ChartImagDeriv.Statement :=
  ChartImagDeriv.proof AnalyticDerivBound.full CuspTimeDeriv.proof

theorem PeriodHermValue.full : PeriodHermValue.Statement := PeriodHermValue.proof

theorem PeriodGramPosDef.full : PeriodGramPosDef.Statement :=
  PeriodGramPosDef.proof PeriodHermValue.full

theorem PivotInvDiag.full : PivotInvDiag.Statement :=
  PivotInvDiag.proof LeadMinorLeading.proof LeadMinorBasic.proof

theorem PivotLast.full : PivotLast.Statement := PivotLast.proof PivotInvDiag.full

theorem PivotBounds.full : PivotBounds.Statement :=
  PivotBounds.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotInvDiag.full PivotLast.full

theorem PivotProductBound.full : PivotProductBound.Statement :=
  PivotProductBound.proof LeadMinorBasic.proof

theorem GramPivotProduct.full : GramPivotProduct.Statement :=
  GramPivotProduct.proof LeadMinorLeading.proof LeadMinorBasic.proof PivotLast.full
    UnimodularLast.proof SchurDetBound.proof IntGramQf.proof IntGramUnimodular.proof
    IntGramDropLast.proof IntGramSubLast.proof

theorem CuspCoordinateBound.full : CuspCoordinateBound.Statement :=
  CuspCoordinateBound.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodGramPosDef.full

theorem ChartBounds.full : ChartBounds.Statement := ChartBounds.proof

theorem ChartGradient.full : ChartGradient.Statement :=
  ChartGradient.proof LogDetGramDeriv.full ChartFrameDeriv.full ChartImagDeriv.full
    ChartBounds.full

theorem LogDetGramPsh.full : LogDetGramPsh.Statement :=
  LogDetGramPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full

theorem ChartPotentialPsh.full : ChartPotentialPsh.Statement :=
  ChartPotentialPsh.proof LogDetGramContinuous.full LogDetGramSubmean.full
    ChartImagContinuous.proof ChartImagMean.proof

theorem SchurQuotient.full : SchurQuotient.Statement := MCSchur.schurQuotient

theorem SchurQuotientPeriod.full : SchurQuotientPeriod.Statement := MCPeriod.schurQuotientPeriod

theorem CuspLattice.full : CuspLattice.Statement :=
  CuspLattice.proof
    (CuspShortVectors.proof ChartPeriodImPos.proof ChartLowerBlockBound.proof PeriodHermValue.full)
    (CuspLeadingMinima.proof ChartPeriodImPos.proof)
    (CuspCovolume.proof ChartPeriodImPos.proof PeriodGramPosDef.full CuspCoordinateBound.full
      PivotBounds.full GramPivotProduct.full PivotProductBound.full
      PeriodLatticeCovolume.proof LeadingCovolume.proof)

end GroundTheory.Heights₂.Heights
