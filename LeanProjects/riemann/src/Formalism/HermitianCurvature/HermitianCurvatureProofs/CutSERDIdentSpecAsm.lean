import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSYReal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSCoordAdj
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSSection
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDOpFF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSFund

namespace Formalism.FourierDecayAlt.P.CutSE

theorem rDIdentSpec_of_open (h0 : RDSOpAv) (h1 : RDSOpR) (h2 : RDSOpRv) (h3 : RDSOpA)
    (hp : RDSPAdj) (hQ : RDSQQAdj) (hX : RDSXiTest) (hP : RDSPair) : RDIdentSpec :=
  rDIdentSpec_of_cut spectral_Y_real h0 h1 h2 h3 spectral_inner_product_linear (rDSCoordAdj_of_p hp) spectral_function_adjoint hQ hX spectral_fundamental_identity spectral_section_identity hP
    radial_residue_formula radial_operator_function_field

end Formalism.FourierDecayAlt.P.CutSE
