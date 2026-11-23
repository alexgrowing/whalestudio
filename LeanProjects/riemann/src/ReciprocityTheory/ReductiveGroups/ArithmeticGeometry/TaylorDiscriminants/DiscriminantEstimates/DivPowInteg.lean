import Mathlib

open MvPolynomial

namespace PI

namespace DivPowInteg

noncomputable def delta {K I J : Type} [CommRing K] [Fintype I] [Fintype J] (κ : I → J → K) :
    MvPolynomial (I ⊕ J) K →ₗ[K] MvPolynomial (I ⊕ J) K :=
  ∑ i, ∑ j, κ i j • ((pderiv (Sum.inl i)).toLinearMap ∘ₗ (pderiv (Sum.inr j)).toLinearMap)

end DivPowInteg

def DivPowInteg : Prop :=
  ∀ (A K I J : Type) [CommRing A] [CommRing K] [Algebra ℚ K] [Algebra A K]
    [Fintype I] [Fintype J] (L : Submodule A K) (κ : I → J → K),
    (∀ i j, κ i j ∈ L) →
    ∀ (P : MvPolynomial (I ⊕ J) A) (n : ℕ),
      (∀ m, (((n.factorial : ℚ)⁻¹ •
          (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P)).coeff m) ∈ L ^ n) ∧
      (((∀ m ∈ P.support, ∑ i, m (Sum.inl i) < n) ∨ (∀ m ∈ P.support, ∑ j, m (Sum.inr j) < n)) →
        (DivPowInteg.delta κ ^ n) (MvPolynomial.map (algebraMap A K) P) = 0)

end PI
