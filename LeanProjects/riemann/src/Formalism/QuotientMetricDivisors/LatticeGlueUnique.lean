import Mathlib
import Formalism.QuotientMetricDivisors.Statement

open Module NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

def glueLat {K : Type} [Field K] [NumberField K] {D : ℕ}
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
    {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite →
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)

def LatticeGlueUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (R R' : Submodule (𝓞 K) (Fin D → K)),
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R = R') ∧
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R ≤ R') ∧
    glueLat (fun _ => R) = R

def LatticeGlueIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 L1 : Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → Submodule.IsLattice K L1 →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      (∀ w ∈ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L1) ∧
      (∀ w ∉ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0)

def LatticeGlueSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ),
    (∀ (L0 : Submodule (𝓞 K) (Fin D → K))
      (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
      Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
      (∀ w, L (conjPl w) = L w) →
      {w : HeightOneSpectrum (𝓞 K) |
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal L0}.Finite →
      Submodule.IsLattice K (glueLat L) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
      glueLat L = ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
    (∀ R R' : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R') → R = R')

def StepBGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    (∃! R : Submodule (𝓞 K) (Fin D → K), ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
    ∀ R : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      Submodule.IsLattice K R ∧
      R = glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R =
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
      {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≠
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι μ0) (abelian₂ μ0))}.Finite

def DivIntoDualGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), {w | μ w ≠ μ0}.Finite →
    ∀ (n : Tup → ℕ) (M : ∀ t, Submodule (𝓞 K) (Fin (n t) → K)),
    (∀ t, Submodule.IsLattice K (M t)) →
    ∀ (π : ∀ t, Matrix (Fin D) (Fin (n t)) K), (∀ t, Function.Surjective (π t).mulVec) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (matLat (π (μ w)) (M (μ w))))

end Formalism.DivisionValues
