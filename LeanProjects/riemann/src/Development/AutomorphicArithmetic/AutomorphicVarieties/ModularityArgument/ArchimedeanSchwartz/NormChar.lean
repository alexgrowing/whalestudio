import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.IndWeakC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ArchimedeanSchwartz.ExpIndep

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

namespace UpperTheory.V.Z.Inf

def SideAt (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (σ : CuspSub K n) : Prop :=
  ∀ m : (K →+* ℂ) → Multiset ℂ, (∀ τ, σ.HasInfChar τ (m τ)) → ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)),
    ∀ S : Finset (HeightOneSpectrum (𝓞 K)), S₀ ⊆ S → ∀ B : HeightOneSpectrum (𝓞 K) → Multiset ℂˣ,
      (∀ w ∉ S, (CG.mk σ).HasSat w (B w)) → Pair (eulerL K (cx B) S) (eulerLd K (cx B) S) (linPoly (∑ τ, m τ))

def SideCen : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n,
    Cm.carrier σ ≤ centralCuspForms K n → SideAt K σ

def Side : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 2 ≤ n → ∀ σ : CuspSub K n, SideAt K σ

def SatBd : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ) (σ : CuspSub K n), ∃ c₀ : ℝ,
    ∀ (w : HeightOneSpectrum (𝓞 K)) (B : Multiset ℂˣ), (CG.mk σ).HasSat w B → ∀ b ∈ B,
      ‖(b : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀ ∧ ‖((b⁻¹ : ℂˣ) : ℂ)‖ ≤ (Ideal.absNorm w.asIdeal : ℝ) ^ c₀

def Union : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (mP : (K →+* ℂ) → Multiset ℂ) (m : (M →+* ℂ) → Multiset ℂ), (∀ φ, P.HasInfChar φ (mP φ)) → (∀ τ, π.HasInfChar τ (m τ)) →
      ∑ φ, mP φ = ∑ τ, m τ

def CharSep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], ∃ χ : HChar K, Function.Injective (expo χ)

def NormChar : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M]
    (χ : HChar K), ∃ ξ : HChar M, (∀ τ, expo ξ τ = expo χ (τ.comp (algebraMap K M))) ∧
      ∀ (w : HeightOneSpectrum (𝓞 M)) (f : ℕ), χ.UnrAt (w.under (𝓞 K)) → normV w = normV (w.under (𝓞 K)) ^ f →
        ξ.UnrAt w ∧ ξ.val w = χ.val (w.under (𝓞 K)) ^ f

def SideOf : Prop := PairOps → SideCen → Side
def UnionOf : Prop := PairOps → Cross → Side → SatBd → Regroup → Union
def InfOf : Prop := Sep → Union → CharSep → NormChar → InfOfLC

end UpperTheory.V.Z.Inf
