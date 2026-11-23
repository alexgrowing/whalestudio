import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.BesselIntegrals.BesselXiIntegrable
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionFunctionalEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.SphericalFunctionLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence

namespace GlobalTheory.HCXi

theorem xiExists_of_besselXiIntegrable : BesselXiIntegrable → Formalism.FourierDecayAlt.B.XiExists := fun h => h

end GlobalTheory.HCXi
