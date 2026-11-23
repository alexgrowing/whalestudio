import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSemiampleNef
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.XMemMIdealOverIff
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Assembly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqSegreRealise
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ChartRingOverOneBlockBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsLast
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfModelNumEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ForSecondHalf

open GroundTheory.Heights₂.Heights.Kleiman

theorem KleimanNefB.segreRealise (hNef : SectionsOverLocalization.NefEq.Statement) (hCh : SectionsOverLocalization.ModelChangeNef.Statement)
    (hNM : SectionsOverLocalization.NumModel.Statement) : SectionsOverLocalization.SegreRealise.Statement :=
  SectionsOverLocalization.SegreRealise.proof SectionsOverLocalization.SegreBase.proof SectionsOverLocalization.SegreTwist.proof SectionsOverLocalization.SegreDim.proof
    (SectionsOverLocalization.SegreNef.proof SectionsOverLocalization.SegreDim.proof SectionsOverLocalization.SegreNum.proof) SectionsOverLocalization.SegreNum.proof
    SectionsOverLocalization.BundleOfDeg.full SectionsOverLocalization.ModelDimEq.full (SectionsOverLocalization.ModelNefEq.proof hNef hCh)
    (SectionsOverLocalization.ModelNumEq.proof hNM)

end GroundTheory.Heights₂.Heights.ForSecondHalf
