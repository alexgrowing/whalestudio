import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Statements
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem PrimeFiltration.proof (hE : PrimeFiltration.Exists.Statement.{u, v, w}) :
    PrimeFiltration.Statement.{u, v, w} :=
  ⟨hE, PrimeFiltration.Irrelevant.proof, PrimeFiltration.Point.proof,
    PrimeFiltration.Restrict.proof⟩

end GroundTheory.Heights₂.Heights.Kleiman
