import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExpansionSiteZeroInduction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEWdExpand
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEIbTInv
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEBTCls
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DecayPairEstimate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.FourierDecayAlt.P5.HerD

theorem expansion_l2_of_open_estimates (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : LevelDensitySquareIntegrable :=
  expansion_L2_of_decay_pairs word_expansion (step_density_expansion_of_mirror boundary_torus_invariance (expansion_site_zero_induction hS hO boundary_torus_closure))
    decay_pair_estimate h2 h3 h4

theorem stepExp0_of_open (hO : OneLetterDens) (hS : DensSmoothCls) (h2 : DecayPair2) (h3 : DecayPair3)
    (h4 : DecayPair4) : StepExp0 :=
  step_density_of_square (expansion_l2_of_open_estimates hO hS h2 h3 h4)

end Formalism.FourierDecayAlt.P.CutSE
