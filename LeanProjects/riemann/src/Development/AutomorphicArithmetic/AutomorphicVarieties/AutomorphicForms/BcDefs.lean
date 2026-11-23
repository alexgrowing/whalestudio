import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.GelfandKazhdanReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsoOfFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Published

namespace UpperTheory.V.Af.Bc

section Defs

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime]

def CharEig (ι : Qbar l ≃+* ℂ) (δ : G F Ω →* (Qbar l)ˣ) (w : HeightOneSpectrum (𝓞 F)) (z : ℂ) : Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := F) A, δ s = 1) ∧
    ∀ σ : G F Ω, IsFrob A (normV w) σ → ι ((δ σ⁻¹ : (Qbar l)ˣ) : Qbar l) = z

theorem charEig_one (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 F)) : CharEig ι (1 : G F Ω →* (Qbar l)ˣ) w 1 :=
  fun _ _ => ⟨fun _ _ => rfl, fun _ _ => by simp⟩

omit [NumberField F] in
variable (F Ω) in

abbrev res (E : Type) [Field E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] : G E Ω →* G F Ω :=
  AlgEquiv.restrictScalarsHom F

omit [NumberField F] in

def IsSign (E : Type) [Field E] [Algebra F E] [Algebra E Ω] [IsScalarTower F E Ω] (δ : G F Ω →* (Qbar l)ˣ) : Prop :=
  (∀ s, δ s = 1 ↔ s ∈ (res F Ω E).range) ∧ ∀ s, δ s = 1 ∨ δ s = -1

abbrev cPl {E : Type} [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  conjSrc (IsCMField.complexConj E).toRingEquiv w

end Defs

def FrobRes : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (w : HeightOneSpectrum (𝓞 E)) (f : ℕ), normV w = normV (w.under (𝓞 F)) ^ f →
    (∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (B : Multiset ℂ),
      FrobEig ι r (w.under (𝓞 F)) B → FrobEig ι (r.comp (res F Ω E)) w (B.map (· ^ f))) ∧
    ∀ (δ : G F Ω →* (Qbar l)ˣ) (z : ℂ), CharEig ι δ (w.under (𝓞 F)) z → CharEig ι (δ.comp (res F Ω E)) w (z ^ f)

def FrobTw : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (r : G F Ω →* GL (Fin n) (Qbar l)) (δ : G F Ω →* (Qbar l)ˣ) (w : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂ) (z : ℂ),
    FrobEig ι r w B → CharEig ι δ w z → FrobEig ι (tw r δ) w (B.map (· * z))

def FrobDual : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (θ : G F Ω →* (Qbar l)ˣ), DualTw r θ →
    ∀ (w : HeightOneSpectrum (𝓞 F)), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ (B : Multiset ℂˣ) (z : ℂˣ),
      FrobEig ι r w (algSat n (normV w) B) → CharEig ι (θ * cycBar F Ω l ^ ((n : ℤ) - 1)) w z →
      B.map (·⁻¹) = B.map (· * z⁻¹)

def SignEx : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime], Module.finrank F E = 2 →
    ∃ δ : G F Ω →* (Qbar l)ˣ, Continuous δ ∧ δ ≠ 1 ∧ IsSign E δ ∧
      ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ A : ValuationSubring Ω, IsPlaceOver A v →
        ∀ s ∈ Ine (F := F) A, δ s = 1

def SignFrob : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω] [Algebra E Ω]
    [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (δ : G F Ω →* (Qbar l)ˣ), IsSign E δ →
    ∀ w : HeightOneSpectrum (𝓞 E),
      (∀ A : ValuationSubring Ω, IsPlaceOver A (w.under (𝓞 F)) → ∀ s ∈ Ine (F := F) A, δ s = 1) →
      CharEig ι δ (w.under (𝓞 F)) (if normV w = normV (w.under (𝓞 F)) then 1 else -1)

def SchurTw : Prop :=
  ∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] [IsAlgClosed k] (n : ℕ) (r : Γ →* GL (Fin n) k) (φ : Γ' →* Γ) (δ : Γ →* kˣ),
    IsIrr (r.comp φ) → δ.comp φ = 1 → RepIso r (tw r δ) → δ = 1

def IrrBasic : Prop :=
  (∀ (Γ Γ' k : Type) [Group Γ] [Group Γ'] [Field k] (n : ℕ) (r : Γ →* GL (Fin n) k),
    (∀ φ : Γ' →* Γ, IsIrr (r.comp φ) → IsIrr r) ∧ (IsIrr r → IsSSRep r) ∧ ∀ δ : Γ →* kˣ, IsSSRep r → IsSSRep (tw r δ)) ∧
  ∀ (Γ k : Type) [Group Γ] [TopologicalSpace Γ] [Field k] [TopologicalSpace k] [IsTopologicalRing k] (n : ℕ)
    (r : Γ →* GL (Fin n) k) (δ : Γ →* kˣ), Continuous r → Continuous δ → Continuous (tw r δ)

def NoTwist : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [Field Ω] [Algebra F E] [Algebra F Ω]
    [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), Module.finrank F E = 2 →
    ∀ (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n), Continuous r → AttR ι r π → IsIrr (r.comp (res F Ω E)) →
      ∀ η : HChar F, IsQuadCharOf E η → ¬ IsoTwist π η

def BcAtt : Prop :=
  ∀ (F E Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsTotallyComplex E] [Field Ω]
    [Algebra F E] [Algebra F Ω] [Algebra E Ω] [IsScalarTower F E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC π P →
      (π.IsRegAlg → (CG.mk P).IsRegAlg) ∧ (AttR ι r π → IsSSRep (r.comp (res F Ω E)) → AttC ι (r.comp (res F Ω E)) P)

def BcConj : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
    (n : ℕ) (π : TR.CuspSub F n) (P : CuspSub E n), IsBC π P →
      ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B, (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (cPl w) B

def ThetaSat : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (P : CuspSub E n) (w : HeightOneSpectrum (𝓞 E))
    (B : Multiset ℂˣ), (CG.mk P).HasSat (cPl w) B → (CG.mk (GlobalTheory.ThetaPull.thetaSub P)).HasSat w (B.map (·⁻¹))

def NormLoc : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ),
    ∃ y : ((w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))ˣ,
      ideleNorm E (localIdele E w x) = localIdele (maximalRealSubfield E) (w.under (𝓞 (maximalRealSubfield E))) y ∧
      ∀ f : ℕ, normV w = normV (w.under (𝓞 (maximalRealSubfield E))) ^ f →
        Valued.v (y : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) =
          Valued.v (x : w.adicCompletion E) ^ f

def NormVal : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (χ : HChar (maximalRealSubfield E)) (w : HeightOneSpectrum (𝓞 E)) (f : ℕ),
    normV w = normV (w.under (𝓞 (maximalRealSubfield E))) ^ f → χ.UnrAt (w.under (𝓞 (maximalRealSubfield E))) →
      (compNorm E χ).UnrAt w ∧ (compNorm E χ).val w = χ.val (w.under (𝓞 (maximalRealSubfield E))) ^ f

def NormGal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    IsLAdicCharOf ι χ μ → ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, (compNorm E χ).UnrAt w ∧
      CharEig ι (μ.comp (res (maximalRealSubfield E) Ω E)) w ((compNorm E χ).val w : ℂˣ)

def CycHecke : Prop :=
  GlobalTheory.Published.GlobalArtinReciprocity → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (wt : ℤ) (θ : G F Ω →* (Qbar l)ˣ), IsCycWt l wt θ →
    Continuous θ ∧ ∃ (χ : HChar F) (art : Ideles F →* Gab F Ω) (a : (F →+* ℂ) → ℤ),
      IsGlobalArtin art ∧ IsAlgPos χ a ∧ IsLAdicOf art ι χ a θ

def SignFix : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E], Module.finrank ℚ E = 2 →
    ∀ [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E)) (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
    IsLAdicCharOf ι χ μ → ∀ n : ℕ, ∃ (χ' : HChar (maximalRealSubfield E)) (μ' : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ),
      IsLAdicCharOf ι χ' μ' ∧ compNorm E χ' = compNorm E χ ∧
      μ'.comp (res (maximalRealSubfield E) Ω E) = μ.comp (res (maximalRealSubfield E) Ω E) ∧
      ∀ v : InfinitePlace (maximalRealSubfield E), χ'.locInf v (-1) = (-1) ^ n

def PolOfSat : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → GlobalTheory.Published.GelfandKazhdanDual →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (P : CuspSub E n) (ψ : HChar E),
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ψ.UnrAt w ∧ ∃ B B', (CG.mk P).HasSat w B ∧ (CG.mk P).HasSat (cPl w) B' ∧
      B'.map (·⁻¹) = B.map (· * (ψ.val w)⁻¹)) → GlobalTheory.ContraPair.DualIsConjBy P ψ

def BcPolar : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K], Module.finrank ℚ K = 2 → ∀ (n : ℕ), 1 ≤ n →
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [Algebra K Ω] [IsScalarTower ℚ K Ω] [IsAlgClosure K Ω]
      (ι : Qbar l ≃+* ℂ) (r : G ℚ Ω →* GL (Fin n) (Qbar l)) (wt : ℤ) (θ : G ℚ Ω →* (Qbar l)ˣ) (π : TR.CuspSub ℚ n),
      Continuous r → AttR ι r π → IsCycWt l wt θ → DualTw r θ → IsIrr (r.comp (res ℚ Ω K)) →
      ∃ (P : CuspSub K n) (χ : HChar (maximalRealSubfield K)) (μ : G (maximalRealSubfield K) Ω →* (Qbar l)ˣ),
        IsBC π P ∧ AttC ι (r.comp (res ℚ Ω K)) P ∧ GlobalTheory.ContraPair.PolarizedPair P χ ∧ IsLAdicCharOf ι χ μ ∧
        μ.comp (res (maximalRealSubfield K) Ω K) = θ.comp (res ℚ Ω K) * cycBar K Ω l ^ ((n : ℤ) - 1)

end UpperTheory.V.Af.Bc
