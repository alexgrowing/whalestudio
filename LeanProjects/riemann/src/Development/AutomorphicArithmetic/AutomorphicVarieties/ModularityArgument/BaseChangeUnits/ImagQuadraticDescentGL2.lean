import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.DescentQOfCyclicRankTwo

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

namespace UpperTheory.V.Z.Bc

def Gap2 {F : Type} [Field F] (inf : (F →+* ℂ) → Multiset ℂ → Prop) : Prop :=
  ∀ τ, ∃ (a : ℂ) (k : ℕ), 2 ≤ k ∧ inf τ {a, a + k}

def ImagQuadraticDescentGL2 : Prop :=
  ∀ (M : Type) [Field M] [NumberField M], Module.finrank ℚ M = 2 → IsTotallyComplex M →
    ∀ sat' inf', IsCusp (F := M) 2 sat' inf' → RegInf 2 inf' → Gap2 inf' →
      (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 ℚ) = w.under (𝓞 ℚ) →
        ∃ B, sat' w B ∧ sat' w' B) →
      ∃ sat inf, IsCusp (F := ℚ) 2 sat inf ∧ WeakBC sat sat' ∧ ∀ τ m, inf' τ m → inf (τ.comp (algebraMap ℚ M)) m

theorem imagQuadDescent_of_descentQ (h : DescQ) : ImagQuadraticDescentGL2 := fun M _ _ h2 hM s i hc hr _ => (h M h2 hM).1 s i hc hr

def GapTwo : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin 2) (Qbar l)) (P : CuspSub F 2), (CG.mk P).IsRegAlg → AttC ι r P →
    (∃ N : ℕ, 0 < N ∧ ∀ s, Matrix.GeneralLinearGroup.det (r s) ^ N = 1) → Gap2 P.HasInfChar

end UpperTheory.V.Z.Bc
