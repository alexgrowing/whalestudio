import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LiftFactorization.PolFalseIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp GlobalTheory.GalCut GlobalTheory.RealGal GlobalTheory.UnitaryBC UpperTheory.V.Published UpperTheory.Gal.UnramifiedFromSplittingCriterion UpperTheory.ConvolutionTheory.Sph

namespace UpperTheory.Gal.AbelianGaloisNormality

def LiftRefl : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (a : ℕ) (π : CuspSub K a), IsLiftUnr π π

def WeakTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a),
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat → WeakBC (CG.mk P).HasSat (CG.mk U).HasSat → WeakBC (CG.mk π).HasSat (CG.mk U).HasSat

def UnrFactor : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L]
    [Algebra K L] [IsScalarTower K M L] (w : HeightOneSpectrum (𝓞 L)), (w.under (𝓞 M)).under (𝓞 K) = w.under (𝓞 K) ∧
    (Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 M) w.asIdeal ∧ Algebra.IsUnramifiedAt (𝓞 K) (w.under (𝓞 M)).asIdeal)

def SplitFactor : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [NumberField L] [Algebra K M] [Algebra M L]
    [Algebra K L] [IsScalarTower K M L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    (i : v.adicCompletion K ≃+* w.adicCompletion L), Continuous i →
    (∀ x : K, i (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) →
    ∃ (u : HeightOneSpectrum (𝓞 M)) (j : v.adicCompletion K ≃+* u.adicCompletion M) (k : u.adicCompletion M ≃+* w.adicCompletion L),
      Continuous j ∧ Continuous k ∧ (∀ x : K, j (algebraMap K _ x) = algebraMap M _ (algebraMap K M x)) ∧
      (∀ x : M, k (algebraMap M _ x) = algebraMap L _ (algebraMap M L x)) ∧ ∀ y, i y = k (j y)

def SplitTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a),
    UpperTheory.CBC.SplitLift (.cx π) (.cx P) → UpperTheory.CBC.SplitLift (.cx P) (.cx U) → UpperTheory.CBC.SplitLift (.cx π) (.cx U)

def LiftTrans : Prop :=
  ∀ (K M L : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field L]
    [NumberField L] [IsTotallyComplex L] [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L] (a : ℕ)
    (π : CuspSub K a) (P : CuspSub M a) (U : CuspSub L a), IsLiftUnr π P → IsLiftUnr P U → IsLiftUnr π U

def PolLift : Prop :=
  ∀ (E M : Type) [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M] [Algebra E M] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (P : CuspSub M a), WeakBC (CG.mk π).HasSat (CG.mk P).HasSat →
    (∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E M))) → ∀ c, Pol c π → Pol c P

def FixLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (g : G K Ω),
    Fixes M g → ∃ g' : G M Ω, AlgEquiv.restrictScalarsHom K g' = g ∧
      ∀ A : ValuationSubring Ω, (g ∈ Dec (F := K) A ↔ g' ∈ Dec (F := M) A) ∧ (g ∈ Ine (F := K) A ↔ g' ∈ Ine (F := M) A)

def PlaceUp : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (A : ValuationSubring Ω),
    (∀ v : HeightOneSpectrum (𝓞 K), IsPlaceOver A v → ∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v ∧ IsPlaceOver A w) ∧
    ∀ w : HeightOneSpectrum (𝓞 M), IsPlaceOver A w → IsPlaceOver A (w.under (𝓞 K))

def SplTrans : Prop :=
  ∀ (K M L Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field L] [Field Ω] [Algebra K M] [Algebra K Ω]
    [Algebra M Ω] [Algebra L Ω] [IsScalarTower K M Ω] (S : Set (HeightOneSpectrum (𝓞 K))) (T : Set (HeightOneSpectrum (𝓞 M))),
    (∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) ∈ S → w ∈ T) → Spl Ω M S → Spl Ω L T → Spl Ω L S

def DisjTrans : Prop :=
  ∀ (K M L Ω : Type) [Field K] [Field M] [Field L] [Field Ω] [Algebra K M] [Algebra M L] [Algebra K Ω] [Algebra M Ω] [Algebra L Ω]
    [IsScalarTower K M Ω] [IsScalarTower M L Ω] (N : Subgroup (G K Ω)), Disjoint' M N →
    GlobalTheory.AboveL.SolvDisj L (N.comap (AlgEquiv.restrictScalarsHom K : G M Ω →* G K Ω)) → Disjoint' L N

def OpenComap : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure K Ω] (N : Subgroup (G K Ω)), IsOpen (N : Set (G K Ω)) →
    IsOpen (N.comap (AlgEquiv.restrictScalarsHom K : G M Ω →* G K Ω) : Set (G M Ω))

def RamLift : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra K M]
    [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure K Ω] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)), IsPlaceOver A v → (∃ τ ∈ Ine (F := K) A, ¬ Fixes M τ) →
    ∀ a : ℕ, 1 ≤ a → ∀ (π : CuspSub K a) (B : Multiset ℂˣ), (CG.mk π).HasSat v B →
    ∃ P : CuspSub M a, IsLiftUnr π P ∧ ∀ c, Pol c π → Pol c P

def StrongOf : Prop := LiftUnr → RamSph → GlobalTheory.Published.ArthurClozelStrongTC

end UpperTheory.Gal.AbelianGaloisNormality
