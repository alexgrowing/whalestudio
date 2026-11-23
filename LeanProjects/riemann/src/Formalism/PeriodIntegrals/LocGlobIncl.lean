import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.ScaledCoordinatesValuationLemma

open NumberField IsDedekindDomain

noncomputable section

namespace PI

def LocGlobIncl : Prop :=
  ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (M B : Submodule (𝓞 K) W) (T : Finset (HeightOneSpectrum (𝓞 K))) (a : HeightOneSpectrum (𝓞 K) → ℤ),
    (∀ w ∈ T, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal
      (Formalism.HermitianLatticesTheory.idealSmul
        (((w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ (-(a w)) :
          FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) B)) →
    (∀ w : HeightOneSpectrum (𝓞 K), w ∉ T →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B) →
    M ≤ Formalism.HermitianLatticesTheory.idealSmul (Formalism.AtG.denIdeal T a : Submodule (𝓞 K) K) B

end PI
