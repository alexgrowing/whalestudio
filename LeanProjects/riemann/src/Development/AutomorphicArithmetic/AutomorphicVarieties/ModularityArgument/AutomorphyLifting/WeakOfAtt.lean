import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.WeightsConjBis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.WitApi
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Win

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def Unl1 (r : G F Ω →* GL (Fin n) (Qbar l)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i j, κ i ≠ κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype

def PotUnl (r : G F Ω →* GL (Fin n) (Qbar l)) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ ∧
    ∀ i j (m : ℕ), 1 ≤ m → κ i ^ m ≠ (κ j * (cycBar F Ω l).comp (Dec (F := F) A).subtype) ^ m

def WitA [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → Unl1 r v → PotUnl r v) ∧
    ∀ π : CuspSub F n, (CG.mk π).IsRegAlg → AttC ι r π → ∃ t : ℝ, ∀ v : HeightOneSpectrum (𝓞 F),
      (((l : ℕ) : 𝓞 F) ∉ v.asIdeal ∨ PotUnl r v) → WinAt π t v

def IneAb (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, (∀ i, Continuous (κ i)) ∧
      ∀ g : ↥(Dec (F := F) A), (g : G F Ω) ∈ Ine (F := F) A →
        (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly = ∏ i, (X - C (κ i g : Qbar l))

def Flagged (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∃ κ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ, IsFlagOn r (Dec (F := F) A) κ

def Keeps (r : G F Ω →* GL (Fin n) (Qbar l)) (L : Type) [Field L] [NumberField L] [Algebra F L] [Algebra L Ω]
    [IsScalarTower F L Ω] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → Unl1 r (w.under (𝓞 F)) →
    Unl1 (r.comp (AlgEquiv.restrictScalarsHom F : G L Ω →* G F Ω)) w

def RowT : Prop := UpperTheory.GalStar.Row0b fun h rc => IsRecT h rc

def PlainRec : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
    ∀ (a : ℕ) (π : CuspSub E a) (t : ℝ), WinAt π t w → ∀ σ, π.IsLocComp w σ →
      GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ UpperTheory.GalStar.Tor (rc (algNorm σ)) ∧ (rc (algNorm σ)).mono0

def Thru (b : Bool) : Prop :=
  RowT → ∀ (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 2 ≤ n →
    ∀ (r : G K Ω →* GL (Fin n) (Qbar l)), Continuous r → IneAb r →
    ∀ P : CuspSub L n, (CG.mk P).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair P χ) →
      AttC ι (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω)) P →
      ∀ v : HeightOneSpectrum (𝓞 K), (((l : ℕ) : 𝓞 K) ∈ v.asIdeal ↔ b = true) → (b = true → PotUnl r v) →
      ∀ (w : PlacesOver L v) (t : ℝ), WinAt P t w.1 → ThruAt P w

def WeakOfAtt : Prop :=
  ∀ (K L Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra K L]
    [Algebra K Ω] [Algebra L Ω] [IsScalarTower K L Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G K Ω →* GL (Fin n) (Qbar l)) (π : CuspSub K n) (P : CuspSub L n), AttC ι r π →
    AttC ι (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω)) P → WeakBC (CG.mk π).HasSat (CG.mk P).HasSat

def FlagLaws : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime] (n : ℕ)
    (r : G K Ω →* GL (Fin n) (Qbar l)),
    (∀ r', RepIso r r' → (IneAb r → IneAb r') ∧ (Flagged r → Flagged r') ∧ ∀ v, (Unl1 r v → Unl1 r' v) ∧ (PotUnl r v → PotUnl r' v)) ∧
    (∀ μ : G K Ω →* (Qbar l)ˣ, (Continuous μ → IneAb r → IneAb (tw r μ)) ∧ (Flagged r → Flagged (tw r μ)) ∧
      ∀ v, (Unl1 r v ↔ Unl1 (tw r μ) v) ∧ (PotUnl r v ↔ PotUnl (tw r μ) v)) ∧
    (∀ (M : ℕ) (m : Fin n → ℤ), 0 < M → Level l M m r → IneAb r ∧ Flagged r) ∧
    ∀ (L : Type) [Field L] [NumberField L] [Algebra K L] [Algebra L Ω] [IsScalarTower K L Ω],
      (IneAb r → IneAb (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω))) ∧
      (Flagged r → Flagged (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω))) ∧
      ∀ w : HeightOneSpectrum (𝓞 L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal →
        (PotUnl r (w.under (𝓞 K)) → PotUnl (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω)) w) ∧
        (Flagged r → (PotUnl (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω)) w → PotUnl r (w.under (𝓞 K))) ∧
          (Unl1 (r.comp (AlgEquiv.restrictScalarsHom K : G L Ω →* G K Ω)) w → Unl1 r (w.under (𝓞 K))))

def AIsoTw : Prop :=
  Hypotheses₂ → ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)), WitA ι r →
    (∀ r', RepIso r r' → WitA ι r') ∧ ∀ μ : G F Ω →* (Qbar l)ˣ, IsAlgChar ι μ → WitA ι (tw r μ)

def AUpDown : Prop :=
  HypothesesH → RowT → ∀ (F K Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field K] [NumberField K] [IsCMField K] [Field Ω]
    [Algebra F K] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure F Ω] [IsGalois F K], Group.IsSolvable (K ≃ₐ[F] K) →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ), 1 ≤ n → ∀ r : G F Ω →* GL (Fin n) (Qbar l), Continuous r →
    IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → Sol.Pol ι r → IsRegAlgAutomorphicAttached ι r → Flagged r →
      (WitA ι r → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) ∧
      (IneAb r → Keeps r K → WitA ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) → WitA ι r)

def ARead : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [IsCMField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : CuspSub F n), (CG.mk π).IsRegAlg → AttC ι r π → WitA ι r →
    ∀ w : HeightOneSpectrum (𝓞 F), (((l : ℕ) : 𝓞 F) ∉ w.asIdeal ∨ Unl1 r w) → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion F) → WD h), IsRecT h rc → ∀ σ, π.IsLocComp w σ →
      GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) ∧ ∀ x : WD h, UpperTheory.GalStar.AwayB x (rc (algNorm σ)) → x = rc (algNorm σ)

theorem aRead_of (H : PlainRec) : ARead := by
  intro F Ω _ _ _ _ _ _ l _ ι n r π hreg ha hW w hw A h rc hrc σ hσ
  obtain ⟨t, ht⟩ := hW.2 π hreg ha
  have hwin : WinAt π t w := ht w (by
    by_cases e : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal
    · exact Or.inr (hW.1 w e (hw.resolve_left fun k => k e))
    · exact Or.inl e)
  obtain ⟨h1, h2, h3⟩ := H F Ω A w h rc hrc n π t hwin σ hσ
  exact ⟨h1, fun x k => k.tor h2 h3⟩

end UpperTheory.V.Z.Win
