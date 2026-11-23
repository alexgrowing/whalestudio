import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz

set_option autoImplicit false

namespace GlobalTheory.Published

open NumberField GlobalTheory.FieldSize

def WeberRayFieldSt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Algebra K ℂ], Module.finrank ℚ K = 2 → discr K < -4 →
    ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, algebraMap K ℂ (a : K) = z) → ∀ n : ℕ, 0 < n →
      ∃ (_ : NumberField (IntermediateField.adjoin K (weberSet L n)))
        (_ : IsAbelianGalois K (IntermediateField.adjoin K (weberSet L n))),
        IsRay (IntermediateField.adjoin K (weberSet L n)) (Ideal.span {(n : 𝓞 K)})

end GlobalTheory.Published
