import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEDecayAsm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWaveOutJ
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSESiteOpsC
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepSquare

namespace Formalism.FourierDecayAlt.P.CutSE

theorem stepExp0_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) : Formalism.FourierDecayAlt.P5.HerD.StepExp0 :=
  stepExp0_of_open hO hS (decayPair2_of_smooth hS) (decayPair3_of wave_outgoing_orbital (clsDecayJ_of hR))
    (decayPair4_of wave_outgoing_orbital (clsDecayJ_of hR) site_multiplication_orbital)

theorem thmPActualCpt_of_leaves (hO : OneLetterDens) (hS : DensSmoothCls) (hR : RadDecay) :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt :=
  Formalism.FourierDecayAlt.P5.HerD.thmPActualCpt_of_stepExp0 (stepExp0_of_leaves hO hS hR)

end Formalism.FourierDecayAlt.P.CutSE
