import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.MassRatio

open NumberField

namespace PIW.CMDiscSq

def RelDiffTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.L2.SG.MassRatio.IsCMPair F E → differentIdeal (𝓞 F) (𝓞 E) = ⊤

def RelDegTwo : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.L2.SG.MassRatio.IsCMPair F E → Module.finrank F E = 2

end PIW.CMDiscSq
