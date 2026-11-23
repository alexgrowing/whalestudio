import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.TwistFactor
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.Gal.InertialTypesAlt.G

section

variable {F : Type} (E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)

def normSet (v : Pl F) : Set (Gw n v) :=
  {g | ∀ η : HChar F, IsNormChar E η → η.loc v (Matrix.GeneralLinearGroup.det g) = 1}

end

def VarEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ P : CuspSub E n, (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) → ∀ (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    ∃ s : Gw n w.1 ≃ₜ* Gw n w.1, IsLocGal σ w (s : Gw n w.1 →* Gw n w.1) ∧ ∀ τ' : SmIrr (Gw n w.1), (Cusp.cx P).locComp w.1 τ' →
      ∃ I : τ'.V ≃ₗ[ℂ] τ'.V, ∀ g x, I (τ'.ρ g x) = τ'.ρ (s g) (I x)

def VarTrace : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), (∀ g : E ≃ₐ[F] E, (Cusp.cx P).ConjIso g.toRingEquiv) →
      WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ (v : Pl F) (w : PlacesOver E v), ¬ GM.Split E v →
    ∀ [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] [MeasurableSpace (Gw n w.1)] [BorelSpace (Gw n w.1)]
      (mF : Measure (Gw n v)) (mE : Measure (Gw n w.1)), mF.IsHaarMeasure → mE.IsHaarMeasure →
    ∀ (τ : SmIrr (Gw n v)) (τ' : SmIrr (Gw n w.1)), (Cusp.cx π).locComp v τ → (Cusp.cx P).locComp w.1 τ' →
    ∀ (s : Gw n w.1 →* Gw n w.1) (I : τ'.V ≃ₗ[ℂ] τ'.V), IsLocGal σ w s → (∀ g x, I (τ'.ρ g x) = τ'.ρ (s g) (I x)) →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ (φ : Gw n w.1 → ℂ) (f : Gw n v → ℂ) (c₁ z : ℂ), Test φ → Test f →
        GM.MatchAt σ v c₁ (fun g => φ (GM.cmp w g)) f → (∀ g, f g ≠ 0 → g ∈ normSet E n v) → HasTrace mF τ.ρ f z →
        HasTwTrace mE τ' I φ (c * c₁ * z)

def MatchCut : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (c : ℂ) (φ : GL (Fin n) (CompletionsOver E v) → ℂ) (f : Gw n v → ℂ),
      (GM.MatchAt σ v c φ f → GM.MatchAt σ v c φ ((normSet E n v).indicator f)) ∧ (Test f → Test ((normSet E n v).indicator f))

def NormInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, GM.Unr E v → ∀ g ∈ GLnLocal.integralGL (v.adicCompletion F) n, g ∈ normSet E n v

end UpperTheory.Gal.InertialTypesAlt.G
