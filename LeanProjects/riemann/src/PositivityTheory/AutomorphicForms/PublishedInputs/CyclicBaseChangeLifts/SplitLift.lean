import PositivityTheory.AutomorphicForms.PublishedInputs.CyclicBaseChange.IsGalAd

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.CBC

namespace Cusp

variable {F : Type} [Field F] [NumberField F] {n : ℕ}

def locComp : Cusp F n → (w : HeightOneSpectrum (𝓞 F)) → SmIrr (GL (Fin n) (w.adicCompletion F)) → Prop
  | cx π => π.IsLocComp
  | re π => π.IsLocComp

end Cusp

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] {n : ℕ}

def SplitLift (π : Cusp K n) (P : Cusp M n) : Prop :=
  ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) (i : v.adicCompletion K ≃+* w.adicCompletion M),
    Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) →
    ∀ σ σ', π.locComp v σ → P.locComp w σ' →
      ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)

def LitCBC2 : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → (IsTotallyReal K ∨ IsTotallyComplex K) → (IsTotallyReal M ∨ IsTotallyComplex M) →
    ∀ n : ℕ, 1 ≤ n →
      (∀ π : Cusp K n, (∃ η : HChar K, IsNormChar M η ∧ (π.twist η).Iso π) ∨
        ∃ P : Cusp M n, WeakBC π.sat P.sat ∧ (∀ τ m, π.inf (τ.comp (algebraMap K M)) m → P.inf τ m) ∧ SplitLift π P) ∧
      (∀ P : Cusp M n, (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) →
        ∃ π : Cusp K n, WeakBC π.sat P.sat ∧ (∀ τ m, P.inf τ m → π.inf (τ.comp (algebraMap K M)) m) ∧ SplitLift π P) ∧
      ∀ (π : Cusp K n) (P : Cusp M n), (∀ σ : M ≃ₐ[K] M, P.ConjIso σ.toRingEquiv) → WeakBC π.sat P.sat →
        (∀ η : HChar K, IsNormChar M η → ¬ (π.twist η).Iso π) ∧
        ∀ π₁ : Cusp K n, WeakBC π₁.sat P.sat → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧ (π.twist η).Iso π₁

end UpperTheory.CBC
