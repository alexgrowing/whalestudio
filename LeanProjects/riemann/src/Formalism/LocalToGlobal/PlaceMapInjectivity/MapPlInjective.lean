import Formalism.ConjugateSelfDual.StatementRest
import Mathlib

noncomputable section

open NumberField IsDedekindDomain Polynomial Filter

namespace Formalism.L2

abbrev Fld : Type := IntermediateField ℚ (AlgebraicClosure ℚ)

def mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) :
    HeightOneSpectrum (𝓞 L) :=
  HeightOneSpectrum.comap ((RingOfIntegers.mapRingEquiv j).symm : 𝓞 L →+* 𝓞 F)
    (RingOfIntegers.mapRingEquiv j).symm.surjective v

theorem mem_mapPl {F L : Type} [Field F] [Field L] (j : F ≃+* L) (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    RingOfIntegers.mapRingEquiv j x ∈ (mapPl j v).asIdeal ↔ x ∈ v.asIdeal := by
  show (RingOfIntegers.mapRingEquiv j).symm (RingOfIntegers.mapRingEquiv j x) ∈ v.asIdeal ↔ _
  rw [RingEquiv.symm_apply_apply]

variable (F : Type) [Field F] [NumberField F] (n : ℕ)

variable {F n}

namespace PreObj

end PreObj

variable (F n)

variable {F n}

namespace RARep

end RARep

variable (F n)

variable {F n}

variable (F n)

variable {F n}

end Formalism.L2
