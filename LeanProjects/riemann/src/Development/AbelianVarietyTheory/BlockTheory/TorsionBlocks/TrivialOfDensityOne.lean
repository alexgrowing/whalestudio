import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DegOneIffSurjective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

def IsUnitaryChar (χ : Ideles L →* ℂˣ) : Prop := ∀ x : Ideles L, ‖((χ x : ℂˣ) : ℂ)‖ = 1

def ValueOneAt (χ : Ideles L →* ℂˣ) (P : HeightOneSpectrum (𝓞 L)) : Prop :=
  UnrAt χ P ∧ ∀ ϖ : (P.adicCompletion L)ˣ,
    Valued.v (ϖ : P.adicCompletion L) = WithZero.exp (-1 : ℤ) → χ (localIdele L P ϖ) = 1

def TrivialOfDensityOneAt (L : Type) [Field L] [NumberField L] : Prop :=
  ∀ χ : Ideles L →* ℂˣ, IsHeckeChar L χ → IsUnitaryChar χ →
    ∀ S : Set (HeightOneSpectrum (𝓞 L)), NumberField.Set.HasDirichletDensity S 1 →
      (∀ P ∈ S, ValueOneAt χ P) → χ = 1

def TrivialOfDensityOne : Prop :=
  ∀ (L : Type) [Field L] [NumberField L], TrivialOfDensityOneAt L

theorem valueOneAt_of_trivAt {χ : Ideles L →* ℂˣ} {P : HeightOneSpectrum (𝓞 L)} (h : TrivAt χ P) :
    ValueOneAt χ P := ⟨h.unrAt, fun ϖ _ => h ϖ⟩

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialOfDensityOneCharacters
