import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesTop
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexMono
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexPi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdPi
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesStdIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealIndexPos
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProductFormula
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealStdIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramPosDef
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramDetChange
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesFischer
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesDiagGram
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGramFischerBound
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesExtendBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesCoordImage
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndex
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexSplit
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesProjIndexLower
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotIndexLog
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotGramLog
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesQuotDegreeBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem LinesLatticeBasis.full : LinesLatticeBasis.Statement :=
  LinesLatticeBasis.proof

theorem LinesGenIndexDet.full : LinesGenIndexDet.Statement :=
  LinesGenIndexDet.proof LinesLatticeBasis.full

theorem LinesIsLattice.full : LinesIsLattice.Statement :=
  LinesIsLattice.proof

theorem LinesGenIndexTrans.full : LinesGenIndexTrans.Statement :=
  LinesGenIndexTrans.proof LinesLatticeBasis.full LinesGenIndexDet.full

theorem LinesGenIndexMono.full : LinesGenIndexMono.Statement :=
  LinesGenIndexMono.proof LinesGenIndexTrans.full

theorem LinesGenIndexPi.full : LinesGenIndexPi.Statement :=
  LinesGenIndexPi.proof

theorem LinesStdPi.full : LinesStdPi.Statement :=
  LinesStdPi.proof

theorem LinesStdIndexDet.full : LinesStdIndexDet.Statement :=
  LinesStdIndexDet.proof LinesGenIndexDet.full

theorem LinesIdealIndexPos.full : LinesIdealIndexPos.Statement :=
  LinesIdealIndexPos.proof LinesIsLattice.full LinesGenIndexTrans.full

theorem LinesProductFormula.full : LinesProductFormula.Statement :=
  LinesProductFormula.proof

theorem LinesIdealLatticeFG.full : LinesIdealLatticeFG.Statement :=
  LinesIdealLatticeFG.proof

theorem LinesIdealStdIndex.full : LinesIdealStdIndex.Statement :=
  LinesIdealStdIndex.proof LinesGenIndexPi.full LinesStdPi.full

theorem LinesGramChange.full : LinesGramChange.Statement :=
  LinesGramChange.proof

theorem LinesGramPosDef.full : LinesGramPosDef.Statement :=
  LinesGramPosDef.proof

theorem LinesGramDetChange.full : LinesGramDetChange.Statement :=
  LinesGramDetChange.proof LinesGramChange.full

theorem LinesFischer.full : LinesFischer.Statement :=
  LinesFischer.proof

theorem LinesDiagGram.full : LinesDiagGram.Statement :=
  LinesDiagGram.proof

theorem LinesGramFischerBound.full : LinesGramFischerBound.Statement :=
  LinesGramFischerBound.proof LinesGramPosDef.full LinesFischer.full LinesDiagGram.full

theorem LinesExtendBasis.full : LinesExtendBasis.Statement :=
  LinesExtendBasis.proof

theorem LinesCoordDet.full : LinesCoordDet.Statement :=
  LinesCoordDet.proof

theorem LinesCoordImage.full : LinesCoordImage.Statement :=
  LinesCoordImage.proof

theorem LinesQuotIndex.full : LinesQuotIndex.Statement :=
  LinesQuotIndex.proof

theorem LinesProjLattice.full : LinesProjLattice.Statement :=
  LinesProjLattice.proof LinesIdealLatticeFG.full

theorem LinesQuotIndexSplit.full : LinesQuotIndexSplit.Statement :=
  LinesQuotIndexSplit.proof LinesQuotIndex.full LinesCoordImage.full LinesCoordDet.full LinesIsLattice.full LinesGenIndexTrans.full LinesStdIndexDet.full LinesProjLattice.full

theorem LinesProjIndexLower.full : LinesProjIndexLower.Statement :=
  LinesProjIndexLower.proof LinesProjLattice.full LinesIdealLatticeFG.full LinesIsLattice.full LinesGenIndexMono.full LinesIdealStdIndex.full

theorem LinesLineDegree.full : LinesLineDegree.Statement :=
  LinesLineDegree.proof

theorem LinesQuotIndexLog.full : LinesQuotIndexLog.Statement :=
  LinesQuotIndexLog.proof LinesQuotIndexSplit.full LinesProjIndexLower.full LinesIdealIndexPos.full LinesProductFormula.full LinesCoordDet.full

theorem LinesQuotGramLog.full : LinesQuotGramLog.Statement :=
  LinesQuotGramLog.proof LinesGramDetChange.full LinesCoordDet.full LinesGramFischerBound.full LinesGramPosDef.full

theorem LinesQuotDegreeBound.full : LinesQuotDegreeBound.Statement :=
  LinesQuotDegreeBound.proof LinesExtendBasis.full LinesQuotIndexLog.full LinesQuotGramLog.full

theorem OrthogonalLines.full : OrthogonalLines.Statement :=
  OrthogonalLines.proof LinesQuotDegreeBound.full LinesLineDegree.full

end GroundTheory.Heights₂.Heights
