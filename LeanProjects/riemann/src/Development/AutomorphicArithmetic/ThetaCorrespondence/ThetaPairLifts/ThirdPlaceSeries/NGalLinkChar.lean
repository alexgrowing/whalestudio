import Formalism.LocalToGlobal.GaloisLevelStructure.LinkChar
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied

set_option synthInstance.maxHeartbeats 200000

section
namespace Formalism.L2
def NGalTiedAlt.TupLink {D : Formalism.BasicNotions.D7} (G : _root_.Formalism.L2.NGalTiedAlt D) {C : Host.CharFrame D} {nch : Formalism.BasicNotions.NChoice D}
    (Tp : Host.TupTied D C nch) : Prop :=
  G.tup = Tp.tup
end Formalism.L2
end
