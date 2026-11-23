import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.CyclicBaseChangeC
import Development.AbelianVarietyTheory.Definitions.Foundations.IsCuspL

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Published

namespace UpperTheory.V.Wt

def ArthurClozel : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → (IsTotallyReal K ∨ IsTotallyComplex K) → (IsTotallyReal M ∨ IsTotallyComplex M) →
    ∀ n : ℕ, 1 ≤ n →
      (∀ sat inf loc, IsCuspL (F := K) n sat inf loc → (∃ η : HChar K, IsNormChar M η ∧ SelfTw sat η) ∨
        ∃ sat' inf' loc', IsCuspL (F := M) n sat' inf' loc' ∧ WeakBC sat sat' ∧ (∀ τ m, inf (τ.comp (algebraMap K M)) m → inf' τ m) ∧
          ∀ (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 M)) (i : v.adicCompletion K ≃+* w.adicCompletion M),
            Continuous i → (∀ x : K, i (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) →
            ∀ σ σ', loc v σ → loc' w σ' →
              ∃ e : σ.V ≃ₗ[ℂ] σ'.V, ∀ g x, e (σ.ρ g x) = σ'.ρ (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x)) ∧
      (∀ sat' inf', Af.IsCusp (F := M) n sat' inf' →
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, Af.IsCusp (F := K) n sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap K M)) m) ∧
      (∀ sat inf sat' inf', Af.IsCusp (F := K) n sat inf → Af.IsCusp (F := M) n sat' inf' → WeakBC sat sat' →
        (∀ η : HChar K, IsNormChar M η → ¬ SelfTw sat η) ∧
        ∀ sat₁ inf₁, Af.IsCusp (F := K) n sat₁ inf₁ → WeakBC sat₁ sat' → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ sat₁ v (B.map (· * η.val v))) ∧
      (∀ sat' inf', Af.IsCusp (F := M) n sat' inf' →
        ¬ (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, Af.IsCusp (F := K) (Module.finrank K M * n) sat inf ∧ (∃ η : HChar K, IsNormChar M η ∧ SelfTw sat η) ∧
          WeakBC sat (fun w B => ∃ B' : (M ≃ₐ[K] M) → Multiset ℂˣ,
            (∀ s : M ≃ₐ[K] M, sat' (GlobalTheory.CuspRep.conjSrc (s : M ≃+* M) w) (B' s)) ∧ B = ∑ᶠ s, B' s) ∧
          ∀ (τ : K →+* ℂ) (m' : (M →+* ℂ) → Multiset ℂ), (∀ τ' : M →+* ℂ, τ'.comp (algebraMap K M) = τ → inf' τ' (m' τ')) →
            inf τ (∑ᶠ (τ' : M →+* ℂ) (_ : τ'.comp (algebraMap K M) = τ), m' τ'))

end UpperTheory.V.Wt
