import Formalism.HermitianCurvature.HermitianCurvatureProofs.Side0PosOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PointLevelZeroEqEmbedding
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ProperDomP

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt

theorem side_zero_of_local_properness (hPr : ProperLeftVariablesDomain) : CutHB.Side0 :=
  CutHB.side_zero_of_positive_and_zero (side0Pos_of'' hPr) (side0Zero_of Formalism.FourierDecayAlt.P.letters_pass_partial_bessel hPr CutHB.pts)

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
