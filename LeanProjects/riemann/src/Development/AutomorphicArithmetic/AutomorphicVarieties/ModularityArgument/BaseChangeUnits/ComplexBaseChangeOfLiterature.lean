import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic
import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChangeLifts.QuadraticBaseChangeOfLiterature

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.V.Z.Bc

def CBCc : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ (∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧ SplitLift π P) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ (∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧ SplitLift π P) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

def CBCr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, RegInf n π.inf → (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ ∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧
      (∀ P : Cusp M n, RegInf n P.inf → (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ ∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

theorem cbcr_of_cbcc (h : CBCc) : CBCr := by
  intro K M _ _ _ _ _ _ hp hK n hn
  obtain ⟨a, b, c⟩ := h K M hp hK n hn
  refine ⟨fun π _ => (a π).imp_right fun ⟨P, h1, h2, _⟩ => ⟨P, h1, h2⟩, fun P _ hP => ?_, fun π P h1 h2 => (c π P h1 h2).2⟩
  obtain ⟨π, h1, h2, _⟩ := b P hP
  exact ⟨π, h1, h2⟩

end UpperTheory.V.Z.Bc
