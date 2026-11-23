import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CycCOfCyclic

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def CyclicRankTwoBaseChange : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyReal K → (IsTotallyReal M ∨ IsTotallyComplex M) →
      (∀ sat inf, IsCusp (F := K) 2 sat inf → RegInf 2 inf → (∃ η : HChar K, IsNormChar M η ∧ SelfTw sat η) ∨
        ∃ sat' inf', IsCusp (F := M) 2 sat' inf' ∧ WeakBC sat sat' ∧ ∀ τ m, inf (τ.comp (algebraMap K M)) m → inf' τ m) ∧
      (∀ sat' inf', IsCusp (F := M) 2 sat' inf' → RegInf 2 inf' →
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, IsCusp (F := K) 2 sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap K M)) m) ∧
      ∀ sat inf sat' inf', IsCusp (F := K) 2 sat inf → IsCusp (F := M) 2 sat' inf' → WeakBC sat sat' →
        ∀ sat₁ inf₁, IsCusp (F := K) 2 sat₁ inf₁ → WeakBC sat₁ sat' → ∃ η : HChar K, (η = 1 ∨ IsNormChar M η) ∧
          ∀ᶠ v : HeightOneSpectrum (𝓞 K) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ sat₁ v (B.map (· * η.val v))

end UpperTheory.V.Z.Bc
