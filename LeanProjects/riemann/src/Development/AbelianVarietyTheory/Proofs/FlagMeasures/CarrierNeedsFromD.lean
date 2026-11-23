import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSETopFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TransferSmoothAtBuiltPlace
import Formalism.HermitianCurvature.JcRadialModuleFormOfParts

namespace GlobalTheory

theorem carrierNeedsFromD :
    Formalism.FourierDecayAlt.P5.ThmPActualCpt ∧ Formalism.FourierDecayAlt.JCT.ModelPlaceBuilt2 ∧ Formalism.FourierDecayAlt.KB.BuiltBounds2Cpt :=
  ⟨Formalism.FourierDecayAlt.P.CutSE.actual_compact_theorem, Formalism.FourierDecayAlt.P.CutMP.SmoothTransferRegularity.model_place_built_holds,
    Formalism.FourierDecayAlt.Final.pb_builtBounds2Cpt⟩

end GlobalTheory
