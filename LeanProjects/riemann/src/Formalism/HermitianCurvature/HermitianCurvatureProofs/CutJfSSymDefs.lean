import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJfSmoothCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

def Xuv (k r : ℕ) (u v : Fin (2 * r + k + 1) → ℂ) : B.Mat k r :=
  vecMulVec u (star (Hpk k r *ᵥ v)) - vecMulVec v (star (Hpk k r *ᵥ u))

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
