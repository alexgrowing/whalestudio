import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAQQ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStable

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

open Formalism.FourierDecayAlt.P.CutMP

theorem jAdjTrQQ_of_open (h1 : JDHatOpQQ) (h7 : JABddOpQQ) (h11 : JAStarOp) (h12 : JAGroupAdj) (h13 : JALocCC) :
    JAdjTrQQ :=
  jAdjTrQQ_of_leaves quadratic_assembly_holds h1 h7 h11 h12 h13 smooth_forms_stability_holds

end Formalism.FourierDecayAlt.P.CutMP.JA
