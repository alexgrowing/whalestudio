import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BorelCasselman
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective

namespace GlobalTheory.Published

theorem BorelCasselman_holds : GlobalTheory.Published.BorelCasselman :=
  fun k _ _ _ _ n _ _ _ V _ _ π hπ =>
    ⟨GlobalTheory.IwahoriInj.iwahoriProj_injective k n V π hπ.1,
      GlobalTheory.SmGL.IwahoriOnto.iwahoriProj_surjective k n V π hπ⟩

end GlobalTheory.Published
