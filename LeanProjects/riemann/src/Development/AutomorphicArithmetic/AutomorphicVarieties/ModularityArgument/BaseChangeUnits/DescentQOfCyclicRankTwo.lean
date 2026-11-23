import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CyclicRankTwoBaseChange

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def DescQ : Prop :=
  ∀ (M : Type) [Field M] [NumberField M], Module.finrank ℚ M = 2 → IsTotallyComplex M →
      (∀ sat' inf', IsCusp (F := M) 2 sat' inf' → RegInf 2 inf' →
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
          ∃ B, sat' w B ∧ sat' w' B) →
        ∃ sat inf, IsCusp (F := ℚ) 2 sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap ℚ M)) m) ∧
      ∀ sat inf sat' inf', IsCusp (F := ℚ) 2 sat inf → IsCusp (F := M) 2 sat' inf' → WeakBC sat sat' →
        ∀ sat₁ inf₁, IsCusp (F := ℚ) 2 sat₁ inf₁ → WeakBC sat₁ sat' → ∃ η : HChar ℚ, (η = 1 ∨ IsNormChar M η) ∧
          ∀ᶠ v : HeightOneSpectrum (𝓞 ℚ) in Filter.cofinite, η.UnrAt v ∧ ∃ B, sat v B ∧ sat₁ v (B.map (· * η.val v))

end UpperTheory.V.Z.Bc
