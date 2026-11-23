import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem host_unr : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE;
    GlobalTheory.UCls.Unr D.host.E := fun D =>
  letI : IsCMField D.host.E := D.host.isCMField_hostE
  Formalism.L2.Pj.unramBridge_holds D.host.E (Formalism.L2.Pj.cmUnram_conj D)

end GlobalTheory.MassLink
