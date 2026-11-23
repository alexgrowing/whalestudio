import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.KatoTwoSOfTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.Imports
import Development.AbelianVarietyTheory.Definitions.Foundations.VanishOrdL
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.GalUnitaryT
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PlainAtR
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.TwNewQ

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Kato.WeilSphericalRecords

def Exact {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] (e : ℕ)
    (r : G F Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := F) A) →* (Qbar l)ˣ) : Prop :=
  IsFlagOn r (Dec (F := F) A) κ ∧ ∀ s : ↥(Dec (F := F) A), (s : G F Ω) ∈ Ine (F := F) A →
    κ 0 s = cycBar F Ω l s ^ (e : ℤ) ∧ κ 1 s = cycBar F Ω l s ^ (-(e : ℤ))

def FrobIn {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (e q : ℕ)
    (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := F) A) →* (Qbar l)ˣ) (B : Multiset ℂˣ) : Prop :=
  ∀ σ : ↥(Dec (F := F) A), IsFrob A q (σ : G F Ω) → ∃ b ∈ algSat 2 q B,
    (q : ℂ) ^ (e : ℤ) * ι ((κ 0 σ * cycBar F Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) * b = 1

def RecSph : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) →
      IsLevelWD 1 n (rc (algNorm σ)) → HasFixed σ.ρ (GlobalTheory.LFun.KGL w n)

def RecFrob : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecT h rc →
    ∀ (n : ℕ) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ),
      GlobalTheory.RoadU.PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) → GlobalTheory.LFun.HasSatGL w σ.ρ B →
      ∀ φ : ↥(Weil h), deg φ = 1 → ∀ z : ℂ, (WD.charPol (rc (algNorm σ)) φ).IsRoot z → ∃ b ∈ algSat n (normV w) B, z * b = 1

def LocK : Prop :=
  ∀ (K Ω : Type) [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (l : ℕ) [Fact l.Prime], l ≠ 2 →
    ∀ (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e → ∀ (r : G K Ω →* GL (Fin 2) (Qbar l)) (P : CuspSub K 2), Continuous r →
    (CG.mk P).IsRegAlg → (∃ χ, GlobalTheory.ContraPair.PolarizedPair P χ) → AttC ι r P →
    ∀ (w : HeightOneSpectrum (𝓞 K)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := K) A) →* (Qbar l)ˣ),
      ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → IsPlaceOver A w → Exact e r A κ → PlainAt P w →
      (∃ B, (CG.mk P).HasSat w B) ∧ ∀ B, (CG.mk P).HasSat w B → FrobIn ι e (normV w) A κ B

def BcSplit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub ℚ 2), Continuous V → IsIrr V →
    (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (GlobalTheory.Ord2.dt V)) → π.IsRegAlg → AttR ι V π →
    ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → IsPlaceOver A v →
    ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : IsCMField K) (_ : Algebra K Ω) (_ : IsScalarTower ℚ K Ω) (_ : IsAlgClosure K Ω)
      (P : CuspSub K 2) (w : HeightOneSpectrum (𝓞 K)), Module.finrank ℚ K = 2 ∧
      IsIrr (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) ∧ (CG.mk P).IsRegAlg ∧
      (∃ χ, GlobalTheory.ContraPair.PolarizedPair P χ) ∧ AttC ι (V.comp (AlgEquiv.restrictScalarsHom ℚ : G K Ω →* G ℚ Ω)) P ∧
      IsPlaceOver A w ∧ ((l : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ normV w = l ∧
      (∀ g ∈ Dec (F := ℚ) A, ∀ x : K, g (algebraMap K Ω x) = algebraMap K Ω x) ∧
      ∀ B, π.HasSat v B ↔ (CG.mk P).HasSat w B

def PotOf : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (e : ℕ), 1 ≤ e →
    ∀ (r : G F Ω →* GL (Fin 2) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω)
      (κ : Fin 2 → ↥(Dec (F := F) A) →* (Qbar l)ˣ), ((l : ℕ) : 𝓞 F) ∈ w.asIdeal → IsPlaceOver A w → Exact e r A κ → PotUnl r w

def LocQ : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (π : TR.CuspSub ℚ 2), Continuous V → IsIrr V →
    (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (GlobalTheory.Ord2.dt V)) → π.IsRegAlg → AttR ι V π →
    ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ),
      ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal → IsPlaceOver A v → Exact e V A κ → (WitAQ ι V ∨ ∃ B, π.HasSat v B) →
      (∃ B, π.HasSat v B) ∧ ∀ B, π.HasSat v B → FrobIn ι e l A κ B

def TwWit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (n : ℕ)
    (W : G ℚ Ω →* GL (Fin n) (Qbar l)) (M : ℕ) (φ : G ℚ Ω →* (Qbar l)ˣ), 1 ≤ M → KillsMu M φ → WitAQ ι W → WitAQ ι (tw W φ)

def SphOfWit : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ), 1 ≤ e →
    ∀ W : G ℚ Ω →* GL (Fin 2) (Qbar l), Continuous W → IsIrr W → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (GlobalTheory.Ord2.dt W)) →
      WitAQ ι W → SphAt ι e W

def FrobRoot : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ)
    (V : G ℚ Ω →* GL (Fin 2) (Qbar l)) (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ) (g : Newform (2 * e + 1)),
    l ≠ 2 → 1 ≤ e → Continuous V → IsIrr V → (∃ M : ℕ, 1 ≤ M ∧ KillsMu M (GlobalTheory.Ord2.dt V)) → GlobalTheory.Ord2.OverL l A → Exact e V A κ →
    g.Att ι (tw V (cycBar ℚ Ω l ^ (-(e : ℤ)))) → ¬ l ∣ g.M → ∀ σ : ↥(Dec (F := ℚ) A), IsFrob A l (σ : G ℚ Ω) →
      ∃ α : ℂ, (g.heckePoly l).IsRoot α ∧ (α = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l) ∨
        α⁻¹ = ι ((κ 0 σ * cycBar ℚ Ω l σ ^ (-(e : ℤ)) : (Qbar l)ˣ) : Qbar l))

def SrcS : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : GlobalTheory.Ord2.R2 Ω l),
    l ≠ 2 → 1 ≤ e → GlobalTheory.Ord2.admitted ι e W → SphAt ι e W → GlobalTheory.Ord2.SrcL ι e W

end UpperTheory.V.Z.Kato.WeilSphericalRecords
