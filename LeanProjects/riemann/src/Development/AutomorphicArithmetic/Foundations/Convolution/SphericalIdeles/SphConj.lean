import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def CBCsph : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M],
    (Module.finrank K M).Prime → IsTotallyComplex K → ∀ n : ℕ, 1 ≤ n → ∀ (π : Cusp K n) (P : Cusp M n), WeakBC π.sat P.sat →
    ∀ v : HeightOneSpectrum (𝓞 K), (∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) →
      (∀ B, π.sat v B → ∀ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v → ∀ f : ℕ, normV w = normV v ^ f →
        P.sat w (B.map (· ^ f))) ∧
      ((∃ w : HeightOneSpectrum (𝓞 M), w.under (𝓞 K) = v ∧ ∃ B', P.sat w B') → ∃ B, π.sat v B)

def PowSat : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (χ : HChar K) (s : ℂ), T.IsPow χ s → ∀ v : Pl K,
    χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = (Ideal.absNorm v.asIdeal : ℂ) ^ (-s)

def SmoEq : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ P P' : CuspSub K n,
    (∀ᶠ w in cofinite, ∃ B, (Cusp.cx P).sat w B ∧ (Cusp.cx P').sat w B) → P = P'

def NormUnr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (η : HChar F),
    IsNormChar E η → ∀ v : Pl F, GM.Unr E v → η.UnrAt v

def SphConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ V : Submodule ℂ (LL μ),
      V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V → ∀ w w' : Pl E, w.under (𝓞 F) = w'.under (𝓞 F) →
      V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥ →
      V ⊓ fixL μ w' (GLnLocal.integralGL (w'.adicCompletion E) n) ≠ ⊥

def Norm : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure]
      (π : CuspSub F n) (P : CuspSub E n), WeakBC (Cusp.cx π).sat (Cusp.cx P).sat →
      ∃ (s : ℂ) (χ : HChar F) (χ' : HChar E) (V : Submodule ℂ (LL μF)) (V' : Submodule ℂ (LL μE)) (θ : Twist μE),
        T.IsPow χ s ∧ T.IsPow χ' s ∧ Dp.Carries μF (π.twist χ) V ∧ Dp.Carries μE (P.twist χ') V' ∧ IsGalTwist σ θ ∧
        V'.map (θ.U : LL μE →ₗ[ℂ] LL μE) = V' ∧ WeakBC (Cusp.cx (π.twist χ)).sat (Cusp.cx (P.twist χ')).sat ∧
        (∀ Λ t, T.AtAE μF V Λ t → T.OffAll F n (bcInf (K := E) Λ) (bcSat t)) ∧ ∀ Λ t, T.AtAE μE V' Λ t → T.OffAll F n Λ t

def Up : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ v : Pl F, GM.Unr E v →
      ∀ B, (Cusp.cx π).sat v B → ∀ w : Pl E, w.under (𝓞 F) = v → ∀ f : ℕ, normV w = normV v ^ f →
        (Cusp.cx P).sat w (B.map (· ^ f))

def Down : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F]
    [IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (π : CuspSub F n) (P : CuspSub E n), WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ v : Pl F, GM.Unr E v →
      (∃ w : Pl E, w.under (𝓞 F) = v ∧ ∃ B', (Cusp.cx P).sat w B') → ∃ B, (Cusp.cx π).sat v B

end UpperTheory.ConvolutionTheory.Sph
