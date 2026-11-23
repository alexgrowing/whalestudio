import Formalism.SatakeDualWeyl.Statement
import Formalism.HermitianLattices.StatementLat

noncomputable section

open Matrix

namespace Formalism.UG

variable {K : Type} [Field K] [StarRing K] {n : Type} [Fintype n] [DecidableEq n]

def gram (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) : Matrix n n K :=
  fun i j => h (Pi.single i 1) (Pi.single j 1)

def glEquiv (g : GL n K) : (n → K) ≃ₗ[K] (n → K) :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv K (n → K) (Matrix.GeneralLinearGroup.toLin g)

def GlEquivApply : Prop :=
  ∀ (K : Type) [Field K] (n : Type) [Fintype n] [DecidableEq n] (g : GL n K) (x : n → K),
    glEquiv g x = (g : Matrix n n K) *ᵥ x

def HformGram : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (x y : n → K),
    h x y = hform (starRingEnd K) (gram h) x y

def HermBridge : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K) (g : GL n K),
    g ∈ UJ (starRingEnd K) (gram h) ↔ glEquiv g ∈ Formalism.HermitianLatticesTheory.isom h

def HermBridgeSurj : Prop :=
  ∀ (K : Type) [Field K] [StarRing K] (n : Type) [Fintype n] [DecidableEq n]
    (h : (n → K) →ₗ⋆[K] (n → K) →ₗ[K] K), ∀ u ∈ Formalism.HermitianLatticesTheory.isom h, ∃ g : GL n K, glEquiv g = u

def StabGmap : Prop :=
  ∀ (K : Type) [Field K] (R : Type) [CommRing R] [Algebra R K] (n : Type) [Fintype n] [DecidableEq n]
    (Λ : Submodule R (n → K)) (g : GL n K),
    g ∈ stabGL Λ ↔ Formalism.HermitianLatticesTheory.gmap (glEquiv g) Λ = Λ

end Formalism.UG
