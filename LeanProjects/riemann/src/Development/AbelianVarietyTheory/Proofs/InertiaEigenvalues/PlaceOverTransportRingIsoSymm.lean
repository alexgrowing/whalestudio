import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInduction
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDTransport

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem isIrreducible_comp {G H V : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (f : G →* H) (hf : Function.Surjective f) (hρ : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp f : Representation ℂ G V) := by
  let e : Subrepresentation (ρ.comp f : Representation ℂ G V) ≃o Subrepresentation ρ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨x, rfl⟩ := hf g
        exact S.apply_mem_toSubmodule x hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => S.apply_mem_toSubmodule (f g) hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
  exact e.isSimpleOrder

def pull (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))
    {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) : WDRep h' V where
  ρ := a.ρ.comp f
  N := a.N
  smooth := hs _ a.ρ a.smooth
  semisimple σ := a.semisimple (f σ)
  nilpotent := a.nilpotent
  comm σ := by
    show a.ρ (f σ) * a.N = _
    rw [a.comm (f σ), hdeg, hq]
    rfl

section Pull

variable (f : Weil h' →* Weil h) (hdeg : ∀ σ, deg (f σ) = deg σ) (hq : normV w = normV w')
    (hs : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g → IsSmooth (g.comp f))

@[simp] theorem pull_ρ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h') : (pull f hdeg hq hs a).ρ σ = a.ρ (f σ) := rfl

@[simp] theorem pull_N {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) : (pull f hdeg hq hs a).N = a.N := rfl

theorem iso_pull {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] {a : WDRep h V} {b : WDRep h V'}
    (hab : a.Iso b) : (pull f hdeg hq hs a).Iso (pull f hdeg hq hs b) := by
  obtain ⟨e, h1, h2⟩ := hab
  exact ⟨e, fun σ v => h1 (f σ) v, h2⟩

def pullWD : WD h → WD h' :=
  Quotient.lift (s := isoSetoid h) (fun a => WD.mk (pull f hdeg hq hs a.2))
    (fun _ _ hab => WD.sound (iso_pull f hdeg hq hs hab))

theorem pullWD_mk {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk (pull f hdeg hq hs a) :=
  WD.sound (iso_pull f hdeg hq hs (WD.iso_std a).symm)

theorem pullWD_eq {V V' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (a : WDRep h V) (b : WDRep h' V')
    (e : V ≃ₗ[ℂ] V') (h1 : ∀ σ v, e (a.ρ (f σ) v) = b.ρ σ (e v)) (h2 : ∀ v, e (a.N v) = b.N (e v)) :
    pullWD f hdeg hq hs (WD.mk a) = WD.mk b := by
  rw [pullWD_mk]; exact WD.sound ⟨e, h1, h2⟩

end Pull

end GlobalTheory.WDTransport

namespace GlobalTheory.WDTransport

open WDRep in

theorem exists_equiv_wd : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (φ : Ω ≃+* Ω') (j : E →+* E') (i : w.adicCompletion E ≃+* w'.adicCompletion E'), PlaceIso A w A' w' φ j i → ∃ S : WD h ≃ WD h', (∀ y y', WDRel φ y y' ↔ S y = y') ∧ (∀ y, (S y).lpDim = y.lpDim) ∧ S (WD.lpZero h) = WD.lpZero h' ∧ (∀ y z, S (y.lpSum z) = (S y).lpSum (S z)) ∧ (∀ y z, S (y.lpChar z) = (S y).lpChar (S z)) ∧ (∀ y (s : ℝ), S (y.lpTw s) = (S y).lpTw s) ∧ (∀ n, S (WD.lpSp h n) = WD.lpSp h' n) ∧ (∀ y, IsIrrWD (S y) ↔ IsIrrWD y) ∧ ∀ (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) (ξ' : Weil h' →* ℂˣ) (hξ' : GlobalTheory.WeilDeligne.IsSmooth ξ'), (∀ σ σ', WeilRel φ σ σ' → ξ σ = ξ' σ') → S (WD.lpOfChar h ξ hξ) = WD.lpOfChar h' ξ' hξ' := by
  intro E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' φ j i hP
  obtain ⟨c, hc, hdegc, hq, hsm⟩ := GlobalTheory.T.place_over_transport_ring_iso E Ω A w h E' Ω' A' w' h' φ j i hP
  have hd1 : ∀ σ, deg (c.symm.toMonoidHom σ) = deg σ := fun σ => by
    have := hdegc (c.symm σ); simp only [MulEquiv.apply_symm_apply] at this
    simpa using this.symm
  have hd1' : ∀ σ, deg (c.symm σ) = deg σ := hd1
  have hs1 : ∀ (M : Type) [Monoid M] (g : Weil h →* M), IsSmooth g →
      IsSmooth (g.comp c.symm.toMonoidHom) := fun M _ g hg => by
    have e : (g.comp c.symm.toMonoidHom).comp c.toMonoidHom = g := by ext σ; simp
    have hg' : IsSmooth ((g.comp c.symm.toMonoidHom).comp c.toMonoidHom) := by rwa [e]
    exact (hsm M _).mpr hg'
  have hs2 : ∀ (M : Type) [Monoid M] (g : Weil h' →* M), IsSmooth g →
      IsSmooth (g.comp c.toMonoidHom) := fun M _ g hg => (hsm M g).mp hg
  have hd2 : ∀ σ, deg (c.toMonoidHom σ) = deg σ := fun σ => hdegc σ
  let F := pullWD c.symm.toMonoidHom hd1 hq.symm hs1
  let B := pullWD c.toMonoidHom hd2 hq hs2
  have hF : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h V),
      F (WD.mk a) = WD.mk (pull c.symm.toMonoidHom hd1 hq.symm hs1 a) := fun a => pullWD_mk _ _ _ _ a
  have hB : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (a : WDRep h' V),
      B (WD.mk a) = WD.mk (pull c.toMonoidHom hd2 hq hs2 a) := fun a => pullWD_mk _ _ _ _ a
  let S : WD h ≃ WD h' :=
    { toFun := F
      invFun := B
      left_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hF, hB]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp, fun v => rfl⟩
      right_inv := fun y => by
        induction y using WD.ind with
        | hP n a =>
          rw [hB, hF]
          exact WD.sound ⟨.refl _ _, fun σ v => by simp, fun v => rfl⟩ }
  have hS : ∀ y, S y = F y := fun _ => rfl
  refine ⟨S, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y y'
    constructor
    · rintro ⟨n, b, b', rfl, rfl, hN, hρ⟩
      rw [hS]
      refine pullWD_eq _ _ _ _ b b' (.refl _ _) (fun σ v => ?_) (fun v => by simp [hN])
      have := hρ (c.symm σ) σ ((hc _ _).mpr (by simp))
      simp [this]
    · rintro rfl
      obtain ⟨n, b, rfl⟩ := WD.exists_rep y
      refine ⟨n, b, pull c.symm.toMonoidHom hd1 hq.symm hs1 b, rfl, (hF b).symm, rfl, fun σ σ' hσ => ?_⟩
      rw [← (hc σ σ').mp hσ]
      simp
  · intro y
    induction y using WD.ind with
    | hP n a => rw [hS, hF, WD.lpDim_mk, WD.lpDim_mk]
  · rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => Subsingleton.elim _ _) (fun v => Subsingleton.elim _ _)
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpSum_mk, hF, hF, hF, WD.lpSum_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y z
    induction y using WD.ind with
    | hP n a =>
    induction z using WD.ind with
    | hP m b =>
      rw [hS, hS, hS, WD.lpChar_mk, hF, hF, hF, WD.lpChar_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => rfl, fun v => rfl⟩
  · intro y s
    induction y using WD.ind with
    | hP n a =>
      rw [hS, hS, WD.lpTw_mk, hF, hF, WD.lpTw_mk]
      exact WD.sound ⟨.refl _ _, fun σ v => by simp [hd1', hq], fun v => rfl⟩
  · intro n
    rw [hS]
    exact pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => by simp [WDRep.spEig, hd1', hq]) (fun v => rfl)
  · intro y
    constructor
    · rintro ⟨n, b, hb, hirr⟩
      refine ⟨n, pull c.toMonoidHom hd2 hq hs2 b, ?_, isIrreducible_comp b.ρ _ c.surjective hirr⟩
      rw [← hB, hb]
      exact S.left_inv y
    · rintro ⟨n, a, rfl, hirr⟩
      exact ⟨n, pull c.symm.toMonoidHom hd1 hq.symm hs1 a, (hF a).symm,
        isIrreducible_comp a.ρ _ c.symm.surjective hirr⟩
  · intro ξ hξ ξ' hξ' hξξ
    rw [hS]
    refine pullWD_eq _ _ _ _ _ _ (.refl _ _) (fun σ v => ?_) (fun v => rfl)
    have := hξξ (c.symm σ) σ ((hc _ _).mpr (by simp))
    simp [this]

end GlobalTheory.WDTransport
