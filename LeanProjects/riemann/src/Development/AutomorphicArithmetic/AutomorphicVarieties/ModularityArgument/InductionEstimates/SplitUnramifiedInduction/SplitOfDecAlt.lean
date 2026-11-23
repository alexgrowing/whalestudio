import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.IwahoriHeckeInjectivity.HeckeInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.GalOfCusp
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Ws UpperTheory.V.Base

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E

def SplitOfDec : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure M Ω] [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)),
    (∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ s ∈ Dec (F := K) A, ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x) →
      UpperTheory.ConvolutionTheory.GM.Split M v

def UnrOfIne : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] [IsAlgClosure M Ω] [IsGalois K M] (v : HeightOneSpectrum (𝓞 K)),
    (∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ s ∈ Ine (F := K) A, ∀ x : M, s (algebraMap M Ω x) = algebraMap M Ω x) →
      UpperTheory.ConvolutionTheory.GM.Unr M v

def SphOfUnr : Prop :=
  ∀ (M Ω : Type) [Field M] [NumberField M] [IsCMField M] [Field Ω] [Algebra M Ω] [IsAlgClosure M Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ (r : G M Ω →* GL (Fin n) (Qbar l)) (π : CuspSub M n), Continuous r → Sol.Pol ι r →
    (CG.mk π).IsRegAlg → AttC ι r π → ∀ w : HeightOneSpectrum (𝓞 M), ((l : ℕ) : 𝓞 M) ∉ w.asIdeal →
    ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := M) A, r s = 1) → ∃ B, (CG.mk π).HasSat w B

def PolMix : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (k₀ : IntermediateField ℚ Ω) [NumberField k₀]
    [IsTotallyReal k₀] (ι : Qbar l ≃+* ℂ) (x : G ℚ Ω →* (Qbar l)ˣ) (k t : ℕ) (r : G k₀ Ω →* GL (Fin 2) (Qbar l)),
    S2.MixDat k₀ ι x k t r → (∃ m : ℕ, 0 < m ∧ x ^ m = 1) → Sol.Pol ι r

def IndAutCs : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → Z.Bc.MixWtC K π →
    SplitBad K π → ∀ R : G K Ω →* GL (Fin 4) (Qbar l), IsSSRep R → Z.Bc.IndCh (galEmb K M Ω) r R → IsAutC ι R

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E
