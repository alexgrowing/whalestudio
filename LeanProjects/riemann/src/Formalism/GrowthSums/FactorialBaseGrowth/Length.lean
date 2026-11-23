import Mathlib

noncomputable section

open scoped Pointwise

namespace Formalism.GrowthSums

namespace ModuleLengthMonotonicity

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

abbrev len (W U : Submodule R X) : ℕ∞ := Module.length R (W ⧸ U.comap W.subtype)

variable [IsDomain R] [IsDiscreteValuationRing R]

end ModuleLengthMonotonicity

end Formalism.GrowthSums
