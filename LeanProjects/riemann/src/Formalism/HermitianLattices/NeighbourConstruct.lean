import Mathlib
import Formalism.HermitianLattices.StatementLat

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

def invIdeal (P : Ideal R) : Submodule R K :=
  ⨅ p ∈ P, (1 : Submodule R K).comap ((LinearMap.mulLeft R (algebraMap R K p)))

def neighbourCore (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  L ⊓ (Submodule.map (Algebra.linearMap R K) (conjIdeal (K := K) P)).comap ((h x).restrictScalars R)

def neighbourOf (h : V →ₗ⋆[K] V →ₗ[K] K) (P : Ideal R) (L : Submodule R V) (x : V) :
    Submodule R V :=
  Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ⊔ neighbourCore h P L x

end Defs

def NeighbourConstruct : Prop :=
  ∀ (R K V : Type) [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module R V]
    [IsScalarTower R K V] (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm → h.Nondegenerate →
    (∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) →
    ∀ (P : Ideal R), P.IsMaximal → P ≠ ⊥ → ∀ L : Submodule R V, Submodule.IsLattice K L →
    IsUnimodular h L → ∀ x ∈ L, x ∉ P • L →
    (∃ r ∈ P * conjIdeal (K := K) P, algebraMap R K r = h x x) →
      Submodule.IsLattice K (neighbourOf h P L x) ∧
      IsIntegralLat h (neighbourOf h P L x) ∧ IsUnimodular h (neighbourOf h P L x) ∧
      IsNeighbour (K := K) P L (neighbourOf h P L x) ∧
      L ⊓ neighbourOf h P L x = neighbourCore h P L x

end Formalism.HermitianLatticesTheory
