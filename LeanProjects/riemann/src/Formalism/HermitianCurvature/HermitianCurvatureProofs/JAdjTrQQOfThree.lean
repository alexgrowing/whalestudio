import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQOpen
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAdjDone

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jAdjTrQQ_of_three (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) : JAdjTrQQ :=
  jAdjTrQQ_of_open h1 h7 h11 group_adjoint_transfer_holds local_class_transfer_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
