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
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransportStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIsoStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLawsStatement

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.FieldCompat

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem repRel_symm {i : k ≃+* k'} {x : IrrGL k} {x' : IrrGL k'} (H : RepRel i x x') : RepRel i.symm x' x := by
  obtain ⟨n, π, π', e, rfl, rfl, he⟩ := H
  refine ⟨n, π', π, e.symm, rfl, rfl, fun g v => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective v
  have hg : GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
    ext a b
    simp [GeneralLinearGroup.map]
  rw [LinearEquiv.symm_apply_eq, e.symm_apply_apply, he, hg]

theorem cls_rep (x : IrrGL k) : cls x.2.rep = x := congrArg (Sigma.mk x.1) x.2.cl_rep

theorem exists_cls {x : IrrGL k} {n : ℕ} (hn : x.1 = n) : ∃ π : IrrRep (GL (Fin n) k), cls π = x := by
  subst hn
  exact ⟨x.2.rep, cls_rep x⟩

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  IrrGL.isCusp_of (π := π.ρ) (hs := π.smooth) (hi := π.irr)

theorem isSmoothChar_comp (i : k' ≃+* k) (hi : Continuous i) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (Units.map i.toRingHom.toMonoidHom)) := by
  have hc : Continuous (Units.map i.toRingHom.toMonoidHom : k'ˣ → kˣ) := Continuous.units_map _ hi
  exact IsOpen.preimage hc hχ

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

def psiMap (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle) :
    AddChar (w'.adicCompletion E') Circle := ψ.compAddMonoidHom i.symm.toAddMonoidHom

theorem psiMap_apply (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle)
    (y : w'.adicCompletion E') : psiMap i ψ y = ψ (i.symm y) := rfl

theorem exists_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {n : ℕ} (hn : y.lpDim = n) :
    ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
      b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ' := by
  obtain ⟨m, b, b', rfl, hb', h1, h2⟩ := H
  obtain rfl : m = n := by simpa using hn
  exact ⟨b, b', rfl, hb', h1, h2⟩

theorem fieldCompatible : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), IsRecLit h rc → IsRecLit h' rc' → FieldCompatible rc rc' := by
  intro hG hC hB hL hLC hLE hBZ E Ω _ _ _ _ _ A w h E' Ω' _ _ _ _ _ A' w' h' rc rc'
    ⟨a, ha, ε, hε, H⟩ ⟨a', ha', ε', hε', H'⟩ φ j i h1 h2 h3 h4 n π π' e he
  have P : PlaceIso A w A' w' φ j i := ⟨h1, h2, h3, h4⟩
  have := charZero_compl w
  have := charZero_compl w'
  have hs : Continuous i.symm := (GlobalTheory.T.continuous_ringEquiv_localField_preserves_valuation _ _ i h3).1
  obtain ⟨T, hT, hTd⟩ := GlobalTheory.T.transportIrrGL_bijective_degree_charZero _ _ i h3
  obtain ⟨hcu, hch⟩ := GlobalTheory.T.transport_keeps_cuspidal_twists_characters _ _ i h3
  obtain ⟨S, hS, hSd, hS0, hSs, hSc, hSt, hSp, hSi, hSo⟩ := GlobalTheory.T.place_over_transport_ring_iso_symm E Ω A w h E' Ω' A' w' h' φ j i P
  have hart := GlobalTheory.T.localArtinMap_unique_transport_placeIso hG hC E Ω A w h E' Ω' A' w' h' φ j i P a a' ha ha'
  have hrel : ∀ x, RepRel i x (T x) := fun x => (hT _ _).2 rfl
  have hcusp : ∀ x, x.IsCusp ↔ (T x).IsCusp := fun x => (hcu _ _ (hrel x)).1
  have hpsi : ∀ ψ : AddChar (w.adicCompletion E) Circle, ∀ x, psiMap i ψ (i x) = ψ x := fun ψ x => by
    rw [psiMap_apply, RingEquiv.symm_apply_apply]
  have M : LawsMin a ha (fun ψ y => ε' E' w' h' (psiMap i ψ) (S y)) (fun x => S.symm (rc' (T x))) := by
    refine ⟨S.symm.bijective.comp (H'.bij.comp T.bijective), fun x => ?_, fun χ hχ => ?_, fun ψ hψ hψ1 m ρ τ hρ => ?_,
      fun x => ?_, fun l x hx => ?_⟩
    · rw [← hSd, S.apply_symm_apply, H'.dim, hTd]
    · have hχ' := isSmoothChar_comp i.symm hs hχ
      have hv : ∀ x, (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (Units.map i.toRingHom.toMonoidHom x) = χ x :=
        fun x => congrArg χ (Units.ext (by simp))
      rw [(hT _ _).1 (hch χ hχ _ hχ' hv), H'.one, Equiv.symm_apply_eq]
      refine (hSo _ _ _ _ fun σ σ' hσ => ?_).symm
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply _ a', hart σ σ' hσ, hv]
    · obtain ⟨ρ', hρ'⟩ := exists_cls (hTd (cls ρ))
      obtain ⟨τ', hτ'⟩ := exists_cls (hTd (cls τ))
      have hc : IsCuspidal ρ'.ρ :=
        ((isCusp_cls ρ').1 (hρ' ▸ (hcusp _).1 ((isCusp_cls ρ).2 ⟨Nat.succ_pos m, hρ⟩))).2
      have hne : psiMap i ψ ≠ 1 := fun h0 => hψ1 (AddChar.ext _ _ fun x => by rw [← hpsi, h0]; rfl)
      have key := H'.eps (psiMap i ψ) (hψ.comp hs) hne m ρ' τ' hc
      rw [hρ', hτ'] at key
      simp only [hSc, S.apply_symm_apply]
      exact GlobalTheory.T.rankin_selberg_epsilon_transport _ _ i.symm hs (psiMap i ψ) ψ (fun _ => rfl) m ρ' ρ τ' τ _
        (repRel_symm (hρ' ▸ hrel _)) (repRel_symm (hτ' ▸ hrel _)) key
    · rw [hcusp, H'.cusp, ← hSi, S.apply_symm_apply]
    · let f : Segment (w.adicCompletion E) → Segment (w'.adicCompletion E') := fun Δ =>
        Segment.ofFirst (T Δ.first) ((hcusp _).1 Δ.isCusp_first) Δ.len Δ.len_pos
      have hl := GlobalTheory.T.isLanglandsData_transport_localFieldIso _ _ i h3 l (l.map f) x (T x)
        (by rw [List.forall₂_map_right_iff, List.forall₂_same]; exact fun Δ _ => ⟨hrel _, rfl⟩) (hrel x) hx
      rw [H'.langlands _ _ hl, Equiv.symm_apply_eq]
      clear hl hx
      induction l with
      | nil => exact hS0.symm
      | cons Δ l ih =>
        simp only [segSum, sumList, List.map_cons, List.foldr_cons] at ih ⊢
        rw [hSs, ← ih, hSc, hSt, hSp, S.apply_symm_apply]
        rfl
  obtain ⟨ψ, hψ, hψ1⟩ := exists_continuous_addChar_ne_one (w.adicCompletion E)
  have hE : ε E w h ψ = fun y => ε' E' w' h' (psiMap i ψ) (S y) := funext fun y =>
    GlobalTheory.T.rec_transport_field_iso hG hC hB hL E Ω A w h E' Ω' A' w' h' φ j i P ε ε' hε hε' ψ _ hψ hψ1 (hpsi ψ) y _ ((hS _ _).2 rfl)
  have hrc := GlobalTheory.T.rec_unique_of_laws hLC hLE hBZ E Ω A w h a ha _ rc _ ψ _ hψ hψ1 hE H.toLawsMin M
  have hπ : T (cls π) = cls π' := (hT _ _).1 ⟨n, π, π', e, rfl, rfl, he⟩
  refine exists_of_wdRel ((hS _ _).2 ?_) (H.dim _)
  rw [congrFun hrc (cls π), S.apply_symm_apply, hπ]

end GlobalTheory.LocLanglands.FieldCompat

end
