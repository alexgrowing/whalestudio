import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeilDeligneParamMonodromyEqZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.TrivialOnInertiaOfUnr
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousAdeleNorm

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

def algNorm {w : HeightOneSpectrum (𝓞 E)} (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    IrrGL (w.adicCompletion E) :=
  (IrrGL.of σ.ρ σ.smooth σ.irred).nu (((1 - (a : ℝ)) / 2 : ℝ) : ℂ)

omit [NumberField E] in

def IsSstAt (P : LocPrime l) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (r : ↥Gw →* GL (Fin a) (Om l)) : Prop :=
  ∃ LL' r', IsModel Bw r LL' r' ∧ IsSst P (Bw.repE LL' r')

variable [IsAlgClosure E Ω] [IsCMField E]

def IsLAdicCharOf (ι : Qbar l ≃+* ℂ) (χ : HChar (maximalRealSubfield E))
    (μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ) : Prop :=
  Continuous μ ∧ ∃ (art : Ideles (maximalRealSubfield E) →* Gab (maximalRealSubfield E) Ω)
    (n : (maximalRealSubfield E →+* ℂ) → ℤ), IsGlobalArtin art ∧ IsAlgPos χ n ∧ IsLAdicOf art ι χ n μ

structure IsAttachedAbove (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l) {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where

  deRham : IsdRAt P Bw (r.comp (Dec (F := E) A).subtype)

  jumps : ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1), IsInduced Bw τ τ' →
    IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)

  iwahori : ∀ σ, π.IsLocComp w σ → PRep.fixed σ.ρ (SmGL.iwahori (w.adicCompletion E) (Fin a)) ≠ ⊥ →
    IsSstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
      ∀ rc, IsRec h rc → wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ → IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype)

structure IsGalRepOf (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where

  cont : Continuous r

  ss : IsSSRep r

  pol : ∃ μ : G (maximalRealSubfield E) Ω →* (Qbar l)ˣ, IsLAdicCharOf ι χ μ ∧ ∀ c : Ω ≃+* Ω, IsCMConjOm E Ω c →
    IsConjDual c r (cycBar E Ω l ^ (1 - (a : ℤ)) * μ.comp (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)))

  away : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι r (rc (algNorm σ))

  pure : ∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w),
    ∃ x : WD h, IsWDOf ι r x ∧ (x.lpTw ((wt : ℝ) / 2)).tempered

  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map fun z => ((a : ℂ) - 1) / 2 - z

  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)

  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw), IsAttachedAbove π ι r HT P h Bw hj

end GlobalTheory.GalOfCusp

namespace GlobalTheory.Published

open GlobalTheory.GalOfCusp

def GaloisRepOfPolarizedCuspidal : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)), (CG.mk π).IsRegAlg → IsPolarized π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ), IsGalRepOf π χ ι r wt HT

theorem GaloisRepOfPolarizedCuspidal.of_isCsd (H : GaloisRepOfPolarizedCuspidal) {E : Type} (Ω : Type) [Field E]
    [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} (hr : (CG.mk π).IsRegAlg) (hc : π.IsCsd) :
    ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT :=
  H E Ω l ι a ha π _ hr (isPolarized_of_isCsd hc)

end GlobalTheory.Published

namespace GlobalTheory.GalOfCusp

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem rec_algNorm {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRec h rc) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) :
    rc (algNorm σ) = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨_, _, _, -, H⟩ := H
  exact H.nu_eq _ _

variable [IsCMField E] {π : CuspSub E a} {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}

theorem IsGalRepOf.wdOf_eq (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) :
    wdOf h hl ι r = (rc (IrrGL.of σ.ρ σ.smooth σ.irred)).lpTw ((1 - (a : ℝ)) / 2) :=
  ((H.away w hl A h rc hrc σ hσ).wdOf_eq hl).trans (rec_algNorm hrc σ)

theorem IsGalRepOf.tempered_wdOf (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    ((wdOf h hl ι r).lpTw ((wt : ℝ) / 2)).tempered := by
  obtain ⟨x, h1, h2⟩ := H.pure w hl A h
  rwa [h1.wdOf_eq hl]

end GlobalTheory.GalOfCusp
