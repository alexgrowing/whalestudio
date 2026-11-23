import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACBump
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACHaarPos
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLACInv

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

theorem avgCutoff_of_smooth (h : ACSmooth) : Formalism.FourierDecayAlt.P.JFxI.AvgCutoff :=
  avgCutoff_of_parts averaging_bump_holds averaging_invariance_holds averaging_integrability_holds averaging_haar_positivity h

theorem sAExh_of_smooth (h : ACSmooth) : SAExh :=
  sAExh_of_avgCutoff (avgCutoff_of_smooth h)

end Formalism.FourierDecayAlt.P.CutMP.JA.SA
