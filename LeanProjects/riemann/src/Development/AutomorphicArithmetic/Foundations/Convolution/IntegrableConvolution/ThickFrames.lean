import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TensSmooth

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

def WordTens : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    ∀ w : List (Option (Ix E n)), ∃ φ : Fin (m + 1) → TI F n, IsTens D φ (GM.word νE aE w) ∧
      ∀ g, GM.word νF aF (w.map (GM.resIx F)) g = cvAll νF m (fun i => φ i) g

def AmpSlot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ) (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    (∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure], GM.AmpFn μE νE aE) ∧
      ∀ (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure], GM.AmpFn μF νF aF

def PairPosition : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyComplex F] [IsTotallyComplex E]
    (σ : E ≃ₐ[F] E) (m : ℕ), Module.finrank F E = m + 1 → ∀ (D : InfD σ m) (n : ℕ) (νE : Measure (archGroup E n)) [νE.IsHaarMeasure]
    (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (b a : TI F n) (aE : TI E n) (aF : TI F n), ArchSlot D νE νF b a aE aF →
    GM.ArchPair σ νE νF aE aF 1

def SplitLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) → ∀ n : ℕ,
    (∃ e : GL (Fin n) (v.adicCompletion F) ≃ₜ* GL (Fin n) (w.1.adicCompletion E), ∀ g, e g = mapGL n (completionMap v w.1) g) ∧
    (∀ g, mapGL n (completionMap v w.1) g ∈ GLnLocal.integralGL (w.1.adicCompletion E) n ↔
      g ∈ GLnLocal.integralGL (v.adicCompletion F) n) ∧
    (∀ g, mapGL n (completionMap v w.1) g ∈ GLnLocal.iwahori (w.1.adicCompletion E) n ↔
      g ∈ GLnLocal.iwahori (v.adicCompletion F) n) ∧
    (∀ ν g, mapGL n (completionMap v w.1) g ∈ GM.iwCoset w.1 ν ↔ g ∈ GM.iwCoset v ν) ∧
    Ideal.absNorm w.1.asIdeal = Ideal.absNorm v.asIdeal

def MatchProd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ m : ℕ, Module.finrank F E = m + 1 → ∀ (n : ℕ) (v : Pl F) (w₀ : PlacesOver E v),
    GM.Split E v → ∃ w : Fin (m + 1) ≃ PlacesOver E v, w 0 = w₀ ∧
      ∀ h : ∀ u : PlacesOver E v, GL (Fin n) (u.1.adicCompletion E) → ℂ, (∀ u, Continuous (h u) ∧ HasCompactSupport (h u)) →
      ∀ [MeasurableSpace (GL (Fin n) (v.adicCompletion F))] [BorelSpace (GL (Fin n) (v.adicCompletion F))]
        (mF : Measure (GL (Fin n) (v.adicCompletion F))), mF.IsHaarMeasure →
        mF (GLnLocal.integralGL (v.adicCompletion F) n) = 1 →
        GM.MatchAt σ v 1 (GM.prodFn h) (cvAll mF m fun i g => h (w i) (mapGL n (completionMap v (w i).1) g))

def UnitSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → ∀ (n : ℕ) (v : Pl F), GM.Split E v →
    GM.MatchAt σ v 1 ((unitSet E n v).indicator 1) ((GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1)

def SphLaws : Prop :=
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) → ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ) (h : GL (Fin n) (w.1.adicCompletion E) → ℂ),
    GM.IsSph w.1 p h → GM.IsSph v p fun g => h (mapGL n (completionMap v w.1) g)) ∧
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K),
    (∀ p h, GM.IsSph (n := n) v p h → Continuous h ∧ HasCompactSupport h) ∧
    (∀ p h h', GM.IsSph (n := n) v p h → GM.IsSph v p h' → h = h') ∧
    ∀ [MeasurableSpace (GL (Fin n) (v.adicCompletion K))] [BorelSpace (GL (Fin n) (v.adicCompletion K))]
      (m : Measure (GL (Fin n) (v.adicCompletion K))), m.IsHaarMeasure → m (GLnLocal.integralGL (v.adicCompletion K) n) = 1 →
      ∀ p p' h h', GM.IsSph (n := n) v p h → GM.IsSph v p' h' → GM.IsSph v (p * p') (cv m h h')

end UpperTheory.ConvolutionTheory.L1
