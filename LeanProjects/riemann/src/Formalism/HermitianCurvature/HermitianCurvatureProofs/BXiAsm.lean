import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsAuxiliaryXi

namespace Formalism.FourierDecayAlt.P.BXiAsm
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem closed_of (hX : XiExists) : LemmaBClosed := Formalism.FourierDecayAlt.P.b_lemmaBClosed_of hX

theorem norm_of (hX : XiExists) : LemmaBNorm :=
  Formalism.FourierDecayAlt.Final.lemma_b_norm_of_parts (closed_of hX) Formalism.FourierDecayAlt.Final.conjugation_invariance_all Formalism.FourierDecayAlt.Final.dilation_jacobian_all
    Formalism.FourierDecayAlt.Final.integral_bound_all

theorem any_of (hX : XiExists) : LemmaBAny :=
  Formalism.FourierDecayAlt.Final.lemma_b_from_norm_bound (norm_of hX) Formalism.FourierDecayAlt.Final.integral_norm_bound_variant_b

end Formalism.FourierDecayAlt.P.BXiAsm

namespace Formalism.FourierDecayAlt.P

theorem b_any_of_xi : Formalism.FourierDecayAlt.B2.LemmaBAny := Formalism.FourierDecayAlt.P.BXiAsm.any_of exists_auxiliary_xi

end Formalism.FourierDecayAlt.P
