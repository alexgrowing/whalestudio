import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ImagQuadraticDescentGL2

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def SplitBC {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (sat : HeightOneSpectrum (𝓞 F) → Multiset ℂˣ → Prop) (satE : HeightOneSpectrum (𝓞 E) → Multiset ℂˣ → Prop) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, normV w = normV (w.under (𝓞 F)) → ∃ B, sat (w.under (𝓞 F)) B ∧ satE w B

def DescS : Prop :=
  ∀ (M : Type) [Field M] [NumberField M], Module.finrank ℚ M = 2 → IsTotallyComplex M →
    ∀ sat' inf', IsCusp (F := M) 2 sat' inf' → RegInf 2 inf' → Gap2 inf' →
      (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
        ∃ B, sat' w B ∧ sat' w' B) →
      ∃ sat inf, IsCusp (F := ℚ) 2 sat inf ∧ SplitBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap ℚ M)) m

end UpperTheory.V.Z.Bc
