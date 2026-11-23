import Mathlib
import Formalism.HermitianLattices.StatementLat

open NumberField IsDedekindDomain

noncomputable section

namespace PI

def LatIdxDet : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V)
    (γ : V ≃ₗ[K] V), Submodule.IsLattice K A →
    Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (A.map ((γ : V →ₗ[K] V).restrictScalars (𝓞 K))) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B →
    Formalism.HermitianLatticesTheory.lidx w.asIdeal A B = - WithZero.log (w.valuation K (LinearMap.det (γ : V →ₗ[K] V)))

end PI
