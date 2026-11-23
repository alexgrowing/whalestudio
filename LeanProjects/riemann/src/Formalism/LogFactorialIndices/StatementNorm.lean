import Mathlib

noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate

def NormRel : Prop :=
  ∀ (L : Type) [Field L] (σ : L →+* ℂ) (c : L →+* L), (∀ x, σ (c x) = conj (σ x)) →
    ∀ (D : ℕ) (Y : Matrix (Fin D) (Fin D) L) (G : Matrix (Fin D) (Fin D) ℂ),
      ((Y.map σ) * G * (Y.map σ).conjTranspose).det = σ (Y.det * c Y.det) * G.det

def NormRelDiv : Prop :=
  ∀ (L : Type) [Field L] (σ : L →+* ℂ) (c : L →+* L), (∀ x, σ (c x) = conj (σ x)) →
    ∀ (D : ℕ) (Y : Matrix (Fin D) (Fin D) L) (G : Matrix (Fin D) (Fin D) ℂ) (κ : ℝ) (z₀ zμ : L),
      κ ≠ 0 → z₀ ≠ 0 → G.det = (κ : ℂ) * σ z₀ →
      ((Y.map σ) * G * (Y.map σ).conjTranspose).det = (κ : ℂ) * σ zμ →
      Y.det * c Y.det = zμ / z₀

def NormRelVal : Prop :=
  ∀ (L : Type) [Field L] (c : L →+* L), (∀ x, c (c x) = x) →
    ∀ (v v' : AddValuation L (WithTop ℤ)), (∀ x, v' (c x) = v x) →
    ∀ (y z₀ zμ : L), z₀ ≠ 0 → c z₀ = z₀ → c zμ = zμ → y * c y = zμ / z₀ →
      v y + v' y + v z₀ = v zμ ∧ v y + v' y + v' z₀ = v' zμ

def IntegralityLocal : Prop :=
  ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K]
    (U Xm Zp E : Type) [AddCommGroup U] [Module K U] [Module O U] [IsScalarTower O K U]
    [AddCommGroup Xm] [Module K Xm] [Module O Xm] [IsScalarTower O K Xm]
    [AddCommGroup Zp] [Module K Zp] [AddCommGroup E] [Module K E]
    (P : U →ₗ[K] Xm →ₗ[K] K) (B : U →ₗ[K] E →ₗ[K] K) (pr : Xm →ₗ[K] Zp) (Z : Submodule K Zp)
    (ι : Zp →ₗ[K] E) (ζ : Oˣ) (N : Submodule O U) (Mt : Submodule O Xm) (abelian₂ : Set Zp) (ϖ : O) (s : ℤ),
    Irreducible ϖ →
    (∀ φ F, pr F ∈ Z → P φ F = algebraMap O K ζ * B φ (ι (pr F))) →
    (∀ φ ∈ N, ∀ F ∈ Mt, ∃ o : O, P φ F = (algebraMap O K ϖ) ^ s * algebraMap O K o) →
    (∀ l ∈ abelian₂, l ∈ Z ∧ ∃ F ∈ Mt, pr F = l) →
    ∀ φ ∈ N, ∀ l ∈ abelian₂, ∃ o : O, B ((algebraMap O K ϖ) ^ (-s) • φ) (ι l) = algebraMap O K o

def LogProductFormula : Prop :=
  ∀ (L : Type) [Field L] [NumberField L] (x : L), x ≠ 0 →
    ∑ σ : L →+* ℂ, Real.log ‖σ x‖ =
      ∑ᶠ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
        (FractionalIdeal.count L 𝔭
            (FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers L)) x) : ℝ) *
          Real.log (Ideal.absNorm 𝔭.asIdeal : ℝ)

end Formalism.LatticeIndexTer
