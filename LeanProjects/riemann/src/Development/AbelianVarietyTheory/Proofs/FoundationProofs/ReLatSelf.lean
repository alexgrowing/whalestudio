import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.VolRatioCompare

open NumberField Formalism.BasicNotions

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def reLat (V : HSpace E) (L : Submodule (𝓞 E) V.V) (h1 : Submodule.IsLattice E L)
    (h2 : Formalism.HermitianLatticesTheory.IsUnimodular V.hT L) : HSpace E :=
  { V with L0 := L, standardTuple_isLattice := h1, baseLattice_isUnimodular := h2 }

end GlobalTheory.VolRatioCompare
