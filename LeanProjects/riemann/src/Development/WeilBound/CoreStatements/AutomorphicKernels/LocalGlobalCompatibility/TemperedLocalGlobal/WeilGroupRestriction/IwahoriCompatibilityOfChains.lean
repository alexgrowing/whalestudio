import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.LocalGlobalOfIwahori
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsUnitarisableTrivChar
import ReciprocityTheory.NeutralLocalFields.GrunwaldWang
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.NormVEqPowResF

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K

structure CMExt (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] where
  M : Type
  [fld : Field M]
  [nf : NumberField M]
  [cm : IsCMField M]
  [alg : Algebra E M]
  [algO : Algebra M Ω]
  [tower : IsScalarTower E M Ω]
  [cl : IsAlgClosure M Ω]

attribute [instance] CMExt.fld CMExt.nf CMExt.cm CMExt.alg CMExt.algO CMExt.tower CMExt.cl

def CMExt.self (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] : CMExt E Ω :=
  { M := E }

section

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

def SmoothSub {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} (V : Subgroup (Weil h)) : Prop :=
  ∃ O : Subgroup (G E Ω), IsOpen (O : Set (G E Ω)) ∧ ∀ σ : Weil h, deg σ = 0 → (σ : G E Ω) ∈ O → σ ∈ V

inductive Chain {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) : Subgroup (Weil h) → Prop
  | top : Chain h ⊤
  | step {U V : Subgroup (Weil h)} : Chain h U → V ≤ U → (V.subgroupOf U).Normal → (V.relIndex U).Prime → SmoothSub V → Chain h V

structure GoodSub (H : Subgroup (G E Ω)) : Prop where
  normal : H.Normal
  isOpen : IsOpen (H : Set (G E Ω))
  cyc : ∃ g : G E Ω, H ⊔ Subgroup.zpowers g = ⊤
  cm : ∀ L : IntermediateField E Ω, H ≤ L.fixingSubgroup → IsCMField L

def TrCond {l a : ℕ} [Fact l.Prime] (r : G E Ω →* GL (Fin a) (Qbar l)) (H : Subgroup (G E Ω)) : Prop :=
  ∀ H₁ H₂ : Subgroup (G E Ω), H ≤ H₁ → H₁ < H₂ → ∃ g ∈ H₂, g ∉ H₁ ∧ (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0

end

section

variable {E : Type} (Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {a : ℕ}

structure IsLift (X : CMExt E Ω) (π : CuspSub E a) (P : CuspSub X.M a) : Prop where
  csd : P.IsCsd
  reg : (CG.mk P).IsRegAlg
  res : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT
    (r' : G X.M Ω →* GL (Fin a) (Qbar l)) wt' HT', IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    IsGalRepOf P (quadChar X.M ^ a) ι r' wt' HT' → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r (resG E g) * p⁻¹

end

def K1 : Prop :=
  ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (S : Type) [Finite S]
    (v : S → HeightOneSpectrum (𝓞 F)) (A : S → ValuationSubring Ω), Function.Injective v → (∀ s, IsPlaceOver (A s) (v s)) →
    ∀ χ : ∀ s, Dec (F := F) (A s) →* ℂˣ, (∀ s, IsOpen ((χ s).ker : Set (Dec (F := F) (A s)))) →
    ∃ ψ : G F Ω →* ℂˣ, IsOpen (ψ.ker : Set (G F Ω)) ∧ (∀ s (g : Dec (F := F) (A s)), ψ g = χ s g) ∧
      ∀ u : InfinitePlace F, u.IsReal → ∀ c : G F Ω, Neutral.GrunwaldWang.IsComplexConjugationAt u c → ψ c = 1

def FieldStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), IsSplitAt w → ∀ V : Subgroup (Weil h), V.Normal → V.index.Prime →
    SmoothSub V → ∀ N : Subgroup (G E Ω), N.Normal → IsOpen (N : Set (G E Ω)) →
    ∃ H : Subgroup (G E Ω), GoodSub H ∧ H ⊔ N = ⊤ ∧ ∀ σ : Weil h, σ ∈ V ↔ (σ : G E Ω) ∈ H

def CyclicCMExtensionExists : Prop := K1 → FieldStep

def FieldSplit : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (_ : IsPlaceOver A w) (N : Subgroup (G E Ω)), N.Normal → IsOpen (N : Set (G E Ω)) →
    ∃ H : Subgroup (G E Ω), GoodSub H ∧ H ⊔ N = ⊤ ∧ Dec (F := E) A ≤ H ∧
      ∀ X : CMExt E Ω, (resG E (E' := X.M) (Ω := Ω)).range = H → ∀ w' : HeightOneSpectrum (𝓞 X.M), IsPlaceOver A w' → IsSplitAt w'

def SimplePoleRescaling : Prop := K1 → FieldSplit

def ContinuousInvariantCoefficients : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (X : CMExt E Ω),
    ∃ (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w'), (IsSplitAt w → IsSplitAt w') ∧
      (∀ p : ℕ, ((p : ℕ) : 𝓞 X.M) ∈ w'.asIdeal ↔ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal) ∧
      ∀ σ : Weil h, σ ∈ (resW h h').range ↔ (σ : G E Ω) ∈ (resG E (E' := X.M) (Ω := Ω)).range

def KillingPolyConst : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l a : ℕ) [Fact l.Prime], 1 ≤ a →
    ∀ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r →
    ∃ N : Subgroup (G E Ω), N.Normal ∧ IsOpen (N : Set (G E Ω)) ∧ ∀ H : Subgroup (G E Ω), H ⊔ N = ⊤ → TrCond r H

def OneStep : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg → ∀ X : CMExt E Ω, IsGalois E X.M → (Module.finrank E X.M).Prime →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
      (∃ g, g ∉ (resG E (E' := X.M) (Ω := Ω)).range ∧ (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace ≠ 0) →
      ∃ P : CuspSub X.M a, IsLift Ω X π P

def WBC : Prop :=
  ∀ (F M : Type) [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M] [IsGalois F M] [IsTotallyComplex F]
    [IsTotallyComplex M], (Module.finrank F M).Prime → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub F n,
      (∃ η : HChar F, η ≠ 1 ∧ η ^ Module.finrank F M = 1 ∧
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ,
          normV w = normV (w.under (𝓞 F)) ^ f → η.val (w.under (𝓞 F)) ^ f = 1) ∧ (π.twist η).Iso π) ∨
      ∃ P : CuspSub M n,
        (∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
          ∃ B, (CG.mk π).HasSat (w.under (𝓞 F)) B ∧ (CG.mk P).HasSat w (B.map (· ^ f))) ∧
        ∀ τ m, π.HasInfChar (τ.comp (algebraMap F M)) m → P.HasInfChar τ m

def ContinuationThroughChart : Prop :=
  GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, ∀ X : CMExt E Ω, IsGalois E X.M → (Module.finrank E X.M).Prime →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT → ∀ η : HChar E, η ≠ 1 → η ^ Module.finrank E X.M = 1 →
      (∀ᶠ w : HeightOneSpectrum (𝓞 X.M) in Filter.cofinite, ∀ f : ℕ,
        normV w = normV (w.under (𝓞 E)) ^ f → η.val (w.under (𝓞 E)) ^ f = 1) → (π.twist η).Iso π →
      ∀ g, g ∉ (resG E (E' := X.M) (Ω := Ω)).range → (r g : Matrix (Fin a) (Fin a) (Qbar l)).trace = 0

def WeakLift {F M : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Algebra F M] [IsTotallyComplex F]
    [IsTotallyComplex M] {n : ℕ} (π : CuspSub F n) (P : CuspSub M n) : Prop :=
  ∀ᶠ w : HeightOneSpectrum (𝓞 M) in Filter.cofinite, ∀ f : ℕ, normV w = normV (w.under (𝓞 F)) ^ f →
    ∃ B, (CG.mk π).HasSat (w.under (𝓞 F)) B ∧ (CG.mk P).HasSat w (B.map (· ^ f))

def InfinitePlaceStep : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (X : CMExt E Ω) (P : CuspSub X.M a),
      (π.IsCsd → WeakLift π P → P.IsCsd) ∧
      ((CG.mk π).IsRegAlg → (∀ τ m, π.HasInfChar (τ.comp (algebraMap E X.M)) m → P.HasInfChar τ m) → (CG.mk P).IsRegAlg)

def FinitePlaceStep : Prop :=
  GlobalTheory.Published.LocalLanglandsGL →
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (X : CMExt E Ω) (P : CuspSub X.M a), WeakLift π P →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT
      (r' : G X.M Ω →* GL (Fin a) (Qbar l)) wt' HT', IsGalRepOf π (quadChar E ^ a) ι r wt HT →
      IsGalRepOf P (quadChar X.M ^ a) ι r' wt' HT' → ∃ p : GL (Fin a) (Qbar l), ∀ g, r' g = p * r (resG E g) * p⁻¹

theorem oneStep_of (hW : WBC) (h3 : ContinuationThroughChart) (h4 : InfinitePlaceStep) (h4' : FinitePlaceStep) (hL : GlobalTheory.Published.LocalLanglandsGL)
    (hJ : GlobalTheory.Published.JacquetShalikaRigidity) : OneStep := by
  intro E Ω _ _ _ _ _ _ a ha π hc hr X hG hp l _ ι r wt HT H ⟨g, hg, ht⟩
  rcases hW E X.M hp a ha π with ⟨η, h1, h2, h3', h4''⟩ | ⟨P, hP, hi⟩
  · exact absurd (h3 hL E Ω a ha π X hG hp l ι r wt HT H η h1 h2 h3' h4'' g hg) ht
  · exact ⟨P, (h4 hJ E Ω a ha π X P).1 hc hP, (h4 hJ E Ω a ha π X P).2 hr hi, h4' hL E Ω a ha π X P hP⟩

def Tower : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)) wt HT,
      IsGalRepOf π (quadChar E ^ a) ι r wt HT → ∀ H : Subgroup (G E Ω), GoodSub H → TrCond r H →
      ∃ (X : CMExt E Ω) (P : CuspSub X.M a), (resG E (E' := X.M) (Ω := Ω)).range = H ∧ IsLift Ω X π P

def LocalHeckeAlgebra : Prop := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.LocalLanglandsGL → OneStep → Tower

def ChainLift : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg → ∀ (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w)
      (U : Subgroup (Weil h)), Chain h U →
      ∃ (X : CMExt E Ω) (P : CuspSub X.M a) (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w'),
        (resW h h').range = U ∧ IsSplitAt w' ∧ IsLift Ω X π P

def WeakLiftRestriction : Prop := GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → FieldStep → FieldSplit → ContinuousInvariantCoefficients → KillingPolyConst → Tower → ChainLift

def K5 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (X : CMExt E Ω) (l a : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r → ∀ (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w'),
    ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ x : WD h, IsWDOf ι r x → IsWDOf ι (r.comp (resG E (E' := X.M))) (WD.res h h' x)

def K6 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (X : CMExt E Ω) (l a : ℕ) [Fact l.Prime]
    (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l)), Continuous r →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w')
    (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) →
    ∃ (O' : Type) (_ : CommRing O') (_ : Algebra ℤ_[l] O') (_ : TopologicalSpace O')
      (Bw' : LocBridge l X.M Ω (Dec (F := X.M) A) O') (hj' : Pst.Induces Bw'),
      IsPstAt P Bw' ((r.comp (resG E (E' := X.M))).comp (Dec (F := X.M) A).subtype) ∧
      wdAt P ι Bw' h' hj' ((r.comp (resG E (E' := X.M))).comp (Dec (F := X.M) A).subtype) =
        WD.res h h' (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype))

def K7 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc →
    ∀ (a : ℕ) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))),
      (∀ t : Weil h, deg t = 0 → (rc (algNorm σ)).charPol t = (X - 1) ^ a) →
      PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥

def Main : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, π.IsCsd → (CG.mk π).IsRegAlg →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)), w ∈ placesOver E l → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw)
      (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), π.IsLocComp w σ →
      ∀ rc : IrrGL (w.adicCompletion E) → WD h, IsRec h rc →
      ∀ U : Subgroup (Weil h), Chain h U → (∀ t ∈ U, deg t = 0 → (rc (algNorm σ)).charPol t = (X - 1) ^ a) →
        ∃ (X : CMExt E Ω) (w' : HeightOneSpectrum (𝓞 X.M)) (h' : IsPlaceOver A w'), (resW h h').range = U ∧
          WD.res h h' (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) = WD.res h h' (rc (algNorm σ))

def IwahoriLocalGlobal : Prop :=
  GlobalTheory.Published.GaloisRepOfPolarizedCuspidal → GlobalTheory.Published.DeRhamPotSemistable → GlobalTheory.Published.LocalLanglandsGL →
    ContinuousInvariantCoefficients → ChainLift → K5 → K6 → K7 → Main

def K9 : Prop := GlobalTheory.Published.DeRhamPotSemistable → Main → LocalGlobalAboveLAlt.IwahoriBaseChange

theorem iwahori_compatibility_of_chains (k1 : K1) (k2a : CyclicCMExtensionExists) (k2b : SimplePoleRescaling) (k2c : ContinuousInvariantCoefficients) (k3a : KillingPolyConst) (k3b : ContinuationThroughChart) (k4a : InfinitePlaceStep) (k4b : FinitePlaceStep) (k5 : K5) (k6 : K6)
    (k7 : K7) (k8a : LocalHeckeAlgebra) (k8b : WeakLiftRestriction) (k8c : IwahoriLocalGlobal) (k9 : K9) (hW : WBC) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal)
    (hB : GlobalTheory.Published.DeRhamPotSemistable) (hL : GlobalTheory.Published.LocalLanglandsGL) (hJ : GlobalTheory.Published.JacquetShalikaRigidity) :
    LocalGlobalAboveLAlt.IwahoriBaseChange :=
  k9 hB (k8c hG hB hL k2c (k8b hG (k2a k1) (k2b k1) k2c k3a (k8a hG hL (oneStep_of hW k3b k4a k4b hL hJ))) k5 k6 k7)

end PositivityTheory.Pf1.CLGD.K

end
