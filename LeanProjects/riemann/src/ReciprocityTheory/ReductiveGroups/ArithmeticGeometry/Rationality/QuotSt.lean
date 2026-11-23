import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

noncomputable def ordAt {R : Type*} [CommRing R] [IsDedekindDomain R] {F : Type*} [Field F]
    [Algebra R F] [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R) (x : F) : ℤ :=
  -WithZero.log (v.valuation F x)

def QuotLocalStatement : Prop :=
  ∀ (O Q : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup Q] [Module O Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) O Q) →
    ∀ (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q),
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      Module.length O (Q ⧸ Submodule.span O (Set.range th)) ≤
        IsDiscreteValuationRing.addVal O (Matrix.of fun i j => c i (th j)).det

def QuotShiftStatement : Prop :=
  ∀ (R F : Type) [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] (v : IsDedekindDomain.HeightOneSpectrum R)
    (Q : Type) [AddCommGroup Q],
    let Rv := (v.valuationSubringAtPrime F).toSubring
    ∀ [Module Rv Q] (ρ : ℕ), Nonempty (Module.Basis (Fin ρ) Rv Q) →
    ∀ (c : Fin ρ → (Q →ₗ[Rv] F)) (s : Fin ρ → ℝ) (β : ℝ) (th : Fin ρ → Q),
      (∀ i q, c i q ≠ 0 → -β ≤ (ordAt v (c i q) : ℝ) + s i) →
      (Matrix.of fun i j => c i (th j)).det ≠ 0 →
      ∃ n : ℕ, Module.length Rv (Q ⧸ Submodule.span Rv (Set.range th)) = n ∧
        (n : ℝ) ≤ (ordAt v (Matrix.of fun i j => c i (th j)).det : ℝ) + ∑ i, s i + ρ * β

def FreeQuotStatement : Prop :=
  ∀ (R F X : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]
    (M₁ : Submodule R X), M₁.FG → ∀ N : Submodule F X,
      Module.Free R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) ∧
      Module.finrank R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) +
          Module.finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) =
        Module.finrank F ↥(Submodule.span F (M₁ : Set X))

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
