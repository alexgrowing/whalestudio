import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Admissible

namespace GlobalTheory.DecInputs

theorem decLow_and_decInf_and_kFinSmooth :
    Formalism.FourierDecayAlt.ThreeDimData.DecLow ∧ Formalism.FourierDecayAlt.ThreeDimData.DecInf ∧ PI.KFinSmooth :=
  ⟨GlobalTheory.DecTransport.decLow_holds, Formalism.L2.SG.BesselDiscreteSeries.decInf,
    Formalism.L2.SG.LitS.kFinSmooth_pi Formalism.L2.SG.Pf.admitted.kFinSmooth'⟩

end GlobalTheory.DecInputs
