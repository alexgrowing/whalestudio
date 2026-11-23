import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocPhi
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocAdd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalSquareIntegrableTransfer

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem jALocCC_of_op (h2 : JALocOp) (h3 : JALocAdj) : JALocCC :=
  jALocCC_of_leaves h2 h3 local_phi_transfer_holds local_additivity_transfer local_square_integrable_transfer

end Formalism.FourierDecayAlt.P.CutMP.JA

end
