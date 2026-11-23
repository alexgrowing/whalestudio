import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

def RealStep (E Ω : Type) {Y : Type} [Field E] [Field Y] [Field Ω] [Algebra E Y] [Algebra Y Ω] (δ : Y) : Prop :=
  (∃ q : ℕ, 0 < q ∧ δ ^ 2 = (q : Y)) ∧ (∀ y : Y, ∃ a b : E, y = algebraMap E Y a + algebraMap E Y b * δ) ∧
    ∃ s : Ω ≃+* Ω, (∀ (j : E →+* Ω) (x : E), s (j x) = j x) ∧ s (algebraMap Y Ω δ) = -algebraMap Y Ω δ

def RamOff {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (T : Set (HeightOneSpectrum (𝓞 F))) (Q : QCM F Ω) :
    Prop :=
  ∃ u ∉ T, ∃ A : ValuationSubring Ω, IsPlaceOver A u ∧ ∃ τ ∈ Ine (F := F) A, ¬ Fixes ↥Q.K τ

def Step0 {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] (T : Set (HeightOneSpectrum (𝓞 E)))
    (Q : QCM E Ω) : Prop :=
  (∃ δ : ↥Q.K, RealStep E Ω δ ∧ ∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t →
      ∀ g ∈ Dec (F := maximalRealSubfield E) A, g (δ : Ω) = δ) ∧
    (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := E) A, Fixes ↥Q.K g) ∧ RamOff T Q

def Step1 {Y Ω : Type} [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] (T : Set (HeightOneSpectrum (𝓞 Y)))
    (Q : QCM Y Ω) : Prop :=
  (∃ x : ↥Q.K, ∃ d : ℕ, 0 < d ∧ x ^ 2 = -(d : ↥Q.K)) ∧ Even (Module.finrank ℚ (maximalRealSubfield ↥Q.K)) ∧
    (∀ t ∈ T, ∀ A : ValuationSubring Ω, IsPlaceOver A t → ∀ g ∈ Dec (F := Y) A, Fixes ↥Q.K g) ∧
    (∀ w : HeightOneSpectrum (𝓞 ↥Q.K), ¬ IsSplitAt w → w.under (𝓞 Y) ∉ T ∧
      Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield ↥Q.K)) w.asIdeal ∧
      ∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ g ∈ Dec (F := Y) A, Fixes ↥Q.K g) ∧ RamOff T Q

def Quad0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → {Q : QCM E Ω | Step0 T Q}.Infinite

def Quad1 : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ T : Set (HeightOneSpectrum (𝓞 Y)), T.Finite →
    {Q : QCM Y Ω | Step1 T Q}.Infinite

def SplitIff : Prop :=
  ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 L)), IsPlaceOver A w → (IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g)

def Quad0Ex : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (T : Set (HeightOneSpectrum (𝓞 E))), T.Finite → ∃ Q : QCM E Ω, Step0 T Q

def Quad1Ex : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ T : Set (HeightOneSpectrum (𝓞 Y)), T.Finite → ∃ Q : QCM Y Ω, Step1 T Q

def InfOf : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (P : QCM F Ω → Prop),
    (∀ S : Set (HeightOneSpectrum (𝓞 F)), S.Finite → ∃ Q, P Q ∧ RamOff S Q) → {Q | P Q}.Infinite

def SqrtFix : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω) (x : Ω) (a : ℤ), x ^ 2 = (a : Ω) →
    (∀ t : ℕ, t.Prime → A.valuation (t : Ω) < 1 → ((8 * t : ℕ) : ℤ) ∣ a - 1 → ∀ g ∈ Dec (F := F) A, g x = x) ∧
    (A.valuation ((2 * a : ℤ) : Ω) = 1 → ∀ τ ∈ Ine (F := F) A, τ x = x)

def DecGen : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ φ : G F Ω, IsFrob A (normV v) φ → ∀ X : Set Ω, X.Finite →
    (∀ τ ∈ Ine (F := F) A, ∀ x ∈ X, τ x = x) → ∀ g ∈ Dec (F := F) A, ∃ k : ℤ, ∀ x ∈ X, g x = (φ ^ k) x

def UnrLarge : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], ∃ B : ℕ, ∀ p : ℕ, p.Prime → B < p →
    ∀ w : HeightOneSpectrum (𝓞 K), ((p : ℕ) : 𝓞 K) ∉ w.asIdeal ^ 2

def MkQ : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (x : Ω) (a : ℤ),
    x ^ 2 = (a : Ω) → (∃ g : G Y Ω, g x ≠ x) →
    ∃ (Q : QCM Y Ω) (hx : x ∈ Q.K), (∀ y : ↥Q.K, ∃ b c : Y, y = algebraMap Y ↥Q.K b + algebraMap Y ↥Q.K c * ⟨x, hx⟩) ∧
      ∀ (F : Type) [Field F] [Algebra F Ω] (g : G F Ω), Fixes Y g → g x = x → Fixes ↥Q.K g

def PrimeWith : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (δ : Ω) (q : ℕ), 0 < q →
    δ ^ 2 = (q : Ω) → ∀ g : Ω ≃+* Ω, g δ = -δ → (∀ (j : Y →+* Ω) (y : Y), g (g (j y)) = j y) →
    ∀ (M : ℕ) (ζ : Ω), 0 < M → IsPrimitiveRoot ζ M → ∀ B : ℕ,
    ∃ p : ℕ, p.Prime ∧ B < p ∧ g ζ = ζ ^ p ∧ ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 →
      ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) → h δ = δ → ∀ y : Y, h (algebraMap Y Ω y) = algebraMap Y Ω y

def TwoPrimes : Prop :=
  ∀ (E Y Ω : Type) [Field E] [NumberField E] [Field Y] [NumberField Y] [Field Ω] [Algebra E Y] [Algebra Y Ω]
    [IsAlgClosure Y Ω] (δ : Y), RealStep E Ω δ → ∀ M B : ℕ, 0 < M →
    ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ B < p₁ ∧ p₁ < p₂ ∧ M ∣ p₁ * p₂ + 1 ∧
      ∀ A : ValuationSubring Ω, A.valuation ((p₁ * p₂ : ℕ) : Ω) < 1 → ∀ h : Ω ≃+* Ω, (∀ z, h z ∈ A ↔ z ∈ A) →
        h (algebraMap Y Ω δ) = algebraMap Y Ω δ → ∀ y : Y, h (algebraMap Y Ω y) = algebraMap Y Ω y

def InertSplit : Prop :=
  ∀ (Y Ω : Type) [Field Y] [NumberField Y] [IsCMField Y] [Field Ω] [Algebra Y Ω] [IsAlgClosure Y Ω] (A : ValuationSubring Ω)
    (u : HeightOneSpectrum (𝓞 Y)), IsPlaceOver A u → ∀ (x : Ω) (a : ℤ), x ^ 2 = (a : Ω) →
    (∀ τ ∈ Ine (F := maximalRealSubfield Y) A, Fixes Y τ ∧ τ x = x) →
    (∃ g ∈ Dec (F := maximalRealSubfield Y) A, ¬ Fixes Y g) → ∀ h ∈ Dec (F := Y) A, h x = x

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
