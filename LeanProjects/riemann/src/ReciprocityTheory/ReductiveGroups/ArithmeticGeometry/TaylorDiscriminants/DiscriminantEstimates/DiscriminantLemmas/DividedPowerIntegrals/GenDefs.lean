import Mathlib

open MvPolynomial

namespace PI.DivPowInteg.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

noncomputable def gdelta (κ : I → J → K) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

noncomputable def dL (κ : I → J → K) (i : I) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ j, κ i j • (pderiv (Sum.inr j)).toLinearMap

noncomputable def dR (κ : I → J → K) (j : J) : MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, κ i j • (pderiv (Sum.inl i)).toLinearMap

end

def PowXL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inl i) * R) =
      X (Sum.inl i) * (gdelta κ ^ (n + 1)) R + (n + 1) • dL κ i ((gdelta κ ^ n) R)

def PowXR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (gdelta κ ^ (n + 1)) (X (Sum.inr j) * R) =
      X (Sum.inr j) * (gdelta κ ^ (n + 1)) R + (n + 1) • dR κ j ((gdelta κ ^ n) R)

def CommL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (i : I)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dL κ i R) = dL κ i ((gdelta κ ^ n) R)

def CommR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) (j : J)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ), (gdelta κ ^ n) (dR κ j R) = dR κ j ((gdelta κ ^ n) R)

def VanL : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ i, m (Sum.inl i) < n) → (gdelta κ ^ n) R = 0

def VanR : Prop :=
  ∀ (K I J : Type) [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K)
    (R : MvPolynomial (I ⊕ J) K) (n : ℕ),
    (∀ m ∈ R.support, ∑ j, m (Sum.inr j) < n) → (gdelta κ ^ n) R = 0

end PI.DivPowInteg.Gen
