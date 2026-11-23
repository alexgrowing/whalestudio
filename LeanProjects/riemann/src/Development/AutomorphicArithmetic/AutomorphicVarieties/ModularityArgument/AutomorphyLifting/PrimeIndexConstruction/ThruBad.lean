import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.MixSeedPAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SplitUnramifiedInduction.SplitOfDecAlt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd

namespace UpperTheory.V.Z.Win.Birth

def AllW {F Ω : Type} [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ π : CuspSub F n, (CG.mk π).IsRegAlg → AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π

theorem AllW.witA {F Ω : Type} [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)} (h : AllW ι r)
    (hp : ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl r v) : WitA ι r :=
  ⟨fun v hv _ => hp v hv, fun π h1 h2 => (h π h1 h2).imp fun _ ht v _ => ht v⟩

def AllC (p : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ),
    (Qbar l ≃+* ℂ) → (G F Ω →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ), 2 ≤ n →
    ∀ ι r, p F Ω l n ι r

def AwOne : Prop := AllC fun F _ _ _ _ _ _ _ _ n ι r => ∀ π : CuspSub F n, AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π → AllW ι r

def AwIso : Prop := AllC fun _ _ _ _ _ _ _ _ _ _ ι r => ∀ r', RepIso r r' → AllW ι r → AllW ι r'

def AwTw : Prop := AllC fun F Ω _ _ _ _ _ l _ _ ι r => ∀ κ : G F Ω →* (Qbar l)ˣ, Sd.IsAlgChar ι κ → IsAutC ι r → AllW ι r → AllW ι (tw r κ)

def AwReal : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)), Continuous r → IsIrr (r.comp (galEmb F E Ω)) → PR ι r → AllW ι (r.comp (galEmb F E Ω))

def AwUp : Prop :=
  UpCyc → ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyComplex F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra F E]
    [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] [IsGalois F E] [Group.IsSolvable (E ≃ₐ[F] E)] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r → IsAutC ι r →
      IsIrr (r.comp (galEmb F E Ω)) → AllW ι r → AllW ι (r.comp (galEmb F E Ω))

def ThruBad : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, Z.InvariantSubmoduleMonicPolynomial.E.SplitBad K π →
    ∀ (v : HeightOneSpectrum (𝓞 K)) (w : GroundTheory.Global.SemiLocal.PlacesOver M v), Z.Gam.ThruAt π w

def AwInd : Prop :=
  ∀ (K M Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Field Ω]
    [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower K M Ω] [IsAlgClosure M Ω], Module.finrank K M = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : CuspSub M 2) (r : G M Ω →* GL (Fin 2) (Qbar l)), AttC ι r π → ImaginaryQuadraticEtaCharacter.AllWin π →
    Z.InvariantSubmoduleMonicPolynomial.E.SplitBad K π → ∀ R : G K Ω →* GL (Fin 4) (Qbar l), Z.Bc.IndCh (galEmb K M Ω) r R → AllW ι R

end UpperTheory.V.Z.Win.Birth
