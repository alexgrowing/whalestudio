import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.SphConj
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight

noncomputable section

open NumberField IsDedekindDomain Filter
open GlobalTheory.CuspRep Formalism.L2.Host Formalism.ConjugateSelfDual UpperTheory.V.Published UpperTheory.CBC

namespace UpperTheory.ConvolutionTheory.Sph

def RamSph : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M] [IsTotallyComplex K]
    [IsTotallyComplex M], (Module.finrank K M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ (π : CuspSub K n) (P : CuspSub M n),
    WeakBC (Cusp.cx π).sat (Cusp.cx P).sat → ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      ∀ B, (Cusp.cx π).sat (w.under (𝓞 K)) B → (Cusp.cx P).sat w B

def NormRam : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M], (Module.finrank K M).Prime →
    ∀ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
      normV w = normV (w.under (𝓞 K)) ∧ (∀ w' : HeightOneSpectrum (𝓞 M), w'.under (𝓞 K) = w.under (𝓞 K) → w' = w) ∧
        ∀ η : HChar K, IsNormChar M η → ¬ η.UnrAt (w.under (𝓞 K))

def Unlinked : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) B,
    (Cusp.cx π).sat v B → ∀ a ∈ B, ∀ b ∈ B, (a : ℂ) ≠ (Ideal.absNorm v.asIdeal : ℂ) * b

structure IsLiftUnr {K M : Type} [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M]
    [Algebra K M] {a : ℕ} (π : CuspSub K a) (P : CuspSub M a) : Prop where
  weak : WeakBC (CG.mk π).HasSat (CG.mk P).HasSat
  sat : ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ) (B : Multiset ℂˣ), Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal →
    normV w = normV (w.under (𝓞 K)) ^ f → (CG.mk π).HasSat (w.under (𝓞 K)) B → (CG.mk P).HasSat w (B.map (· ^ f))
  inf : ∀ τ : M →+* ℂ, (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap K M))
  loc : SplitLift (Cusp.cx π) (Cusp.cx P)

def LiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    [IsGalois K M], (Module.finrank K M).Prime → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∀ η : HChar K, IsNormChar M η → (CG.mk π).twist η ≠ CG.mk π) → ∃ P : CuspSub M a, IsLiftUnr π P

def QuadLiftUnr : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ a : ℕ, 1 ≤ a → ∀ π : CuspSub K a,
    (∃ w : HeightOneSpectrum (𝓞 M), ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal ∧ ∃ B, (CG.mk π).HasSat (w.under (𝓞 K)) B) →
    ∃ P : CuspSub M a, IsLiftUnr π P

end UpperTheory.ConvolutionTheory.Sph
