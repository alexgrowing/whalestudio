import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.WeakOfAtt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.GaloisRepRankTwoRealOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SolCOfSolDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ShapeFacts

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open GroundTheory.Global.SemiLocal UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

def PlainAtR {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (π : TR.CuspSub F n) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)

def PlainAt {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} (π : CuspSub K n) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ, π.IsLocComp v σ → GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred)

def PlainR {F : Type} [Field F] [NumberField F] [IsTotallyReal F] {n : ℕ} (π : TR.CuspSub F n) : Prop :=
  ∀ v, PlainAtR π v ∨ ∃ B, π.HasSat v B

def IsCompl {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {v : HeightOneSpectrum (𝓞 F)}
    {w : HeightOneSpectrum (𝓞 E)} (i : v.adicCompletion F ≃+* w.adicCompletion E) : Prop :=
  Continuous i ∧ ∀ x : F, i (algebraMap F _ x) = algebraMap E _ (algebraMap F E x)

def WinPt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ π : CuspSub K n,
    ∃ t : ℝ, ∀ v, PlainAt π v → ImaginaryQuadraticEtaCharacter.WinAt π t v

def PlainOf : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub K n) v,
    (∀ t, ImaginaryQuadraticEtaCharacter.WinAt π t v → PlainAt π v) ∧ ((∃ B, (CG.mk π).HasSat v B) → PlainAt π v)

def SplitTr : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E] (n : ℕ), 1 ≤ n →
    ∀ (π : TR.CuspSub F n) (P : CuspSub E n), IsBC π P → ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
      (i : v.adicCompletion F ≃+* w.adicCompletion E), IsCompl i →
      (PlainAtR π v ↔ PlainAt P w) ∧ ((∃ B, π.HasSat v B) → ∃ B, (CG.mk P).HasSat w B)

def SplitCM : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)), IsIrr (r.comp (resG F E Ω)) → ∀ v : HeightOneSpectrum (𝓞 F),
    ∃ (E' M : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (_ : Field M) (_ : NumberField M) (_ : IsCMField M)
      (_ : Algebra F E') (_ : Algebra E' Ω) (_ : IsScalarTower F E' Ω) (_ : Algebra F M) (_ : Algebra E M) (_ : Algebra E' M) (_ : Algebra M Ω)
      (_ : IsScalarTower F E M) (_ : IsScalarTower F E' M) (_ : IsScalarTower F M Ω) (_ : IsScalarTower E M Ω) (_ : IsScalarTower E' M Ω),
      Module.finrank F E' = 2 ∧ Module.finrank E M = 2 ∧ Module.finrank E' M = 2 ∧ IsIrr (r.comp (resG F M Ω)) ∧
        ∀ w : HeightOneSpectrum (𝓞 E'), w.under (𝓞 F) = v → ∃ i : v.adicCompletion F ≃+* w.adicCompletion E', IsCompl i

def ThruTr : Prop :=
  ∀ (F E E' M : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Field E'] [NumberField E'] [IsTotallyComplex E']
    [Field M] [NumberField M] [IsTotallyComplex M] [Algebra F E] [Algebra F E'] [Algebra F M] [Algebra E M] [Algebra E' M]
    [IsScalarTower F E M] [IsScalarTower F E' M] (n : ℕ) (Q : CuspSub M n) (w : HeightOneSpectrum (𝓞 E)) (w' : HeightOneSpectrum (𝓞 E'))
    (u : PlacesOver M w) (u' : PlacesOver M w'), u.1 = u'.1 → ∀ i : (w'.under (𝓞 F)).adicCompletion F ≃+* w'.adicCompletion E', IsCompl i →
    ThruAt Q u' → ThruAt Q u

def AttBC : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsTotallyComplex L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (P : CuspSub L n), AttC ι r π → AttC ι (r.comp (resG K L Ω)) P →
    WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

def RealUp : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub F 2), Continuous r → π.IsRegAlg → AttR ι r π → IsIrr (r.comp (resG F E Ω)) →
    ∀ P : CuspSub E 2, (CG.mk P).IsRegAlg → AttC ι (r.comp (resG F E Ω)) P → ∀ w : HeightOneSpectrum (𝓞 E),
      (PlainAtR π (w.under (𝓞 F)) ∨ ∃ B, π.HasSat (w.under (𝓞 F)) B) → PlainAt P w

def RealDown : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure F Ω], Module.finrank F E = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub F 2), Continuous r → π.IsRegAlg → (∃ χ, π.Polarized χ) → AttR ι r π →
    IsIrr (r.comp (resG F E Ω)) → IneAb r → ∀ P : CuspSub E 2, (CG.mk P).IsRegAlg → AttC ι (r.comp (resG F E Ω)) P →
    ∀ v : HeightOneSpectrum (𝓞 F), (((l : ℕ) : 𝓞 F) ∈ v.asIdeal → PotUnl r v) →
      (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → PlainAt P w) → PlainAtR π v

end UpperTheory.V.Z.Win
