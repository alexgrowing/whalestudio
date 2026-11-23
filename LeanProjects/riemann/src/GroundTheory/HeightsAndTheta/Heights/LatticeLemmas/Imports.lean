import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Assembly
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawBasic
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawFirstCoord
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem SphereLawBasic.full : SphereLawBasic.Statement := SphereLawBasic.proof

theorem SphereLawFirstCoord.full : SphereLawFirstCoord.Statement := SphereLawFirstCoord.proof

theorem FibreMahlerForms.full : FibreMahlerForms.Statement := FibreMahlerForms.proof

theorem SpherePhase.full : SpherePhase.Statement :=
  SpherePhase.full_of_sphereLawBasic SphereLawBasic.full

theorem SphereProjectionLaw.full : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.full_of SphereLawBasic.full SphereLawFirstCoord.full

theorem PointwiseLelong.full : PointwiseLelong.Statement :=
  PointwiseLelong.full_of SphereLawBasic.full SphereLawFirstCoord.full

theorem HeightOfCycle.full : HeightOfCycle.Statement :=
  HeightOfCycle.full_of_fibreMahlerForms FibreMahlerForms.full

end GroundTheory.Heights₂.Heights
