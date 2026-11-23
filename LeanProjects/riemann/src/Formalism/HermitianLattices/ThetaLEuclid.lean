import Mathlib
import Formalism.HermitianLattices.StatementTheta
import Formalism.HermitianLattices.GenusCovolBound

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def ThetaLEuclid : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
    (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      thetaL h L γ τ = thetaE (zmap ι L) (ι γ) τ

def ThetaLSLaw : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V),
      ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)],
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      thetaL h L γ (-τ⁻¹) =
        (-Complex.I * τ) ^ ((N : ℂ) / 2) / (ZLattice.covolume (zmap ι L) : ℂ) *
          ∑' μ : tdualSub h L,
            Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ μ) : ℚ) : ℂ)) *
            Complex.exp (Real.pi * Complex.I * τ * ((Algebra.trace ℚ K (h μ μ) : ℚ) : ℂ))

end Formalism.HermitianLatticesTheory
