import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnrSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SymmetricCubeUnits.Sym3AutKOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TwistedAutomorphicForms.EqOneOfMemLev

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Pl

def LemTWM : Prop :=
  ∀ (F L Ω : Type) [Field F] [NumberField F] [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra F L] [Algebra F Ω]
    [Algebra L Ω] [IsScalarTower F L Ω] [IsAlgClosure F Ω] [IsAlgClosure L Ω], IsTotallyReal F → Module.finrank F L = 2 →
    ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 3 ≤ M → ∀ Φ : Set (HeightOneSpectrum (𝓞 L)), Af.Tw.IsType F M Φ →
    ∀ ν : G F Ω →* (Qbar l)ˣ, Continuous ν → (∀ c, IsConjEl c → ν c = 1) →
      (∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
        ∀ s ∈ Ine (F := F) A, ν s = 1) →
      ∃ κ : G L Ω →* (Qbar l)ˣ, Continuous κ ∧ VerEq κ ν ∧ ∃ k : ℕ, 0 < k ∧
        ∀ (w : HeightOneSpectrum (𝓞 L)) (A : ValuationSubring Ω), IsPlaceOver A w → ∀ s ∈ Ine (F := L) A,
          (((M : ℕ) : 𝓞 L) ∉ w.asIdeal → κ s = 1) ∧ (w ∉ Φ → κ s ^ k = 1)

def AutTw : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω]
    [IsAlgClosure ℚ Ω] [Algebra K Ω] [Algebra L Ω] [IsAbelianGalois ℚ L] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω),
    Sd.IsCC c → Module.finrank ℚ K = 2 → galOf ℚ L Ω ≤ galOf ℚ K Ω →
    ∀ (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)) (κ : G L Ω →* (Qbar l)ˣ), Continuous ρ → IsAutR ι ρ → IrrOpen ρ → Sd.IsAlgChar ι κ →
    (∀ s s' : G L Ω, galEmb ℚ L Ω s' = c * galEmb ℚ L Ω s * c⁻¹ →
      Matrix.GeneralLinearGroup.det (ρ (galEmb ℚ L Ω s)) * (κ s * κ s') = (cycBar L Ω l s)⁻¹) →
    IsAutCsd ι (tw (ρ.comp (galEmb ℚ L Ω)) κ)

def SeedIn : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : G ℚ Ω) (N w : ℕ)
    (χ' η θ : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), FieldPairCharacterTripleConditions K L c N w χ' η θ j → ∀ M : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M →
    (∀ A : ValuationSubring Ω, ¬ A.valuation (M : Ω) < 1 → ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1) →
    ∀ (m : ℕ) (ρ : G ℚ Ω →* GL (Fin 2) (Qbar l)), 2 ≤ m → EisRep ι (χ' * η) θ (m + 1) ρ → IrrOpen ρ → (χ' * η) c = (-1) ^ (m + 1) →
    ∃ κ : G L Ω →* (Qbar l)ˣ, AdIn ι M m (tw (ρ.comp (galEmb ℚ L Ω)) κ)

def LinkUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    (η : G ℚ Ω →* ℤˣ) (Ψ : G ℚ Ω →* Oˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ)
    (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField O)),
    Pr.GalLink η Ψ σ g₁ B M L Φ → UnrSplit L M

def ChiUnr : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c : Coef l) (N : ℕ) [NeZero N] (e : ℕ)
    (ψ : DirichletCharacter c.O N) (χ' : G ℚ Ω →* (Qbar l)ˣ) (j : ℕ), ¬ l ∣ orderOf χ' →
    (∀ s, ‖((cycBar ℚ Ω l ^ j * χ') s).val - (Chr.Psi l e (Chr.dirG ℚ Ω ψ) s).val.1‖ < 1) →
    ∀ M : ℕ, l * N ∣ M → ∀ (L : Type) [Field L] [NumberField L] [Algebra L Ω] (A : ValuationSubring Ω), ¬ A.valuation (M : Ω) < 1 →
      ∀ s ∈ Ine (F := L) A, χ' (galEmb ℚ L Ω s) = 1

def LinkedEndE : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N), 1 ≤ e → Even N →
  ∀ (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), l * N ∣ M →
    (∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ η.ker → B'.valuation (M : Ω) < 1) →
  ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : Pr.GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), B.valuation (l : Ω) < 1 → Φ.Ok C₀ → Φ.Big C₀ →
    Pr.SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    Pr.FinPt c.O Φ 3 ∧ Pr.AutPt k 3 ι (cycBar L Ω l)⁻¹ ∧ ∃ ka, Sd.IsAlgChar ι ka ∧ Pr.AutPt k 2 ι ka

theorem linkedEndE_of (h : Pr.LinkedEnd) : LinkedEndE :=
  fun Ω _ _ _ l _ ι c _ N _ e ψ he _ => h Ω l ι c N e ψ he

end UpperTheory.V.Z.Sym.Pl

end
