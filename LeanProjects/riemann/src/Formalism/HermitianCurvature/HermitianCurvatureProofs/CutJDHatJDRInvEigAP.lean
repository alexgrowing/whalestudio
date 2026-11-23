import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEig
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvEigA

namespace Formalism.FourierDecayAlt.P.CutMP

theorem inverse_alpha_positive_holds : RInvAlphaP := by
  intro k r z' w m hz' hw hm M _ _ X
  exact InvEig.usage₅ hz' ((m * w)⁻¹) (InvEigA.inverse_product_block_zero hw hm) (InvEigA.det_inverse_product_block hw hm)
    (InvEigA.zeta_fix hz' hw hm) M X

end Formalism.FourierDecayAlt.P.CutMP
