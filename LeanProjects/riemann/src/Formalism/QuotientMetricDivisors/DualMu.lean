import Mathlib
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HarderNarasimhan.QuotRealize

open Module NumberField

noncomputable section

namespace Formalism.DivisionValues

def DualMu : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (D : ℕ), 0 < D →
    ∀ X : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ, (∀ v, IsUnit (X v).det) →
    ∀ R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R →
      Formalism.HN.muDef (Pi.basisFun K (Fin D)).dualBasis (Formalism.HN.dualFrame X) (Formalism.HN.dualLat R) =
        lcv X R / D

end Formalism.DivisionValues
