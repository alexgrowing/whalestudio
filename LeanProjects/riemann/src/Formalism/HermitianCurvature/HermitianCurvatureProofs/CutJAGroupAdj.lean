import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGroupAdjPair
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGACutGraded

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAGroupAdj_of_jComm (h : GA.GAJComm) : JAGroupAdj :=
  GA.jAGroupAdj_of_leaves GA.graded_truncation_action_holds h GA.group_action_pairing_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
