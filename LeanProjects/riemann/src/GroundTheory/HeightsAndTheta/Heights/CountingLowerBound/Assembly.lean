import Mathlib
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallLast
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PReductionSmallFirst
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PInteriorDichotomy
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PAvoidMatrixLemma
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMinkowskiCovolumeBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PCuspWeightBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PShortVectorsOrthogonal
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PPackingCount
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCountBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTailBound
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanLogPlus
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PMeanCuspWeight
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PTelescopeMetric
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.PLimitInEpsilon
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

universe u

theorem ReductionSmallLast.full : ReductionSmallLast.Statement :=
  ReductionSmallLast.proof

theorem ReductionSmallFirst.full : ReductionSmallFirst.Statement :=
  ReductionSmallFirst.proof

theorem InteriorDichotomy.full : InteriorDichotomy.Statement :=
  InteriorDichotomy.proof

theorem AvoidMatrixLemma.full : AvoidMatrixLemma.Statement :=
  AvoidMatrixLemma.proof

theorem MinkowskiCovolumeBound.full : MinkowskiCovolumeBound.Statement.{u} :=
  MinkowskiCovolumeBound.proof

theorem CuspWeightBound.full : CuspWeightBound.Statement :=
  CuspWeightBound.proof

theorem ShortVectorsOrthogonal.full : ShortVectorsOrthogonal.Statement :=
  ShortVectorsOrthogonal.proof

theorem PackingCount.full : PackingCount.Statement :=
  PackingCount.proof

theorem MeanCountBound.full : MeanCountBound.Statement.{u} :=
  MeanCountBound.proof

theorem TailBound.full : TailBound.Statement.{u} :=
  TailBound.proof MeanCountBound.full

theorem MeanLogPlus.full : MeanLogPlus.Statement.{u} :=
  MeanLogPlus.proof TailBound.full

theorem MeanCuspWeight.full : MeanCuspWeight.Statement :=
  MeanCuspWeight.proof

theorem TelescopeMetric.full : TelescopeMetric.Statement :=
  TelescopeMetric.proof

theorem LimitInEpsilon.full : LimitInEpsilon.Statement :=
  LimitInEpsilon.proof

end GroundTheory.Heights₂.Heights.LowerBound
