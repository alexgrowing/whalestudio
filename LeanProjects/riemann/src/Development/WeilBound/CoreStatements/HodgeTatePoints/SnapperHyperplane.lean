import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PMixedTwistShift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplane
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperHyperplaneMid
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperSectionX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDiffPoly
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubsetDiffConst
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumEventual
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterSumTopVanish
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

theorem snapperHyperplane : SnapperHyperplane.Statement.{u, w} :=
  SnapperHyperplane.proof SnapperQuotAdd.closed SnapperQuotDevissage.closed SnapperHyperplaneMid.proof

theorem mixedTwistShift : MixedTwistShift.Statement.{u, w} :=
  MixedTwistShift.proof snapperHyperplane SnapperSection.full SnapperDiffPoly.proof RestrLenEuler.proof
    SubsetDiffConst.proof

theorem interNumEventual : InterNumEventual.Statement.{u, w} :=
  InterNumEventual.proof snapperHyperplane SnapperSection.full

theorem interNumAdditive : InterNumAdditive.Statement.{u, w} :=
  InterNumAdditive.proof interNumEventual (InterSumTopVanish.proof mixedTwistShift)

end PositivityTheory.HtPt.Kra
