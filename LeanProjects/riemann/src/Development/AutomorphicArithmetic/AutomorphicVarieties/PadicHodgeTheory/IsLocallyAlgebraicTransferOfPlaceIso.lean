import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IotaSpec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInverseLocalArtinWeilGroupHom
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InverseLocalArtinContinuousOnInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIso
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W

section
variable {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  [Algebra M Ω] [IsAlgClosure M Ω] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M}
  {h : IsPlaceOver A v} {h' : IsPlaceOver A w}

private theorem locAlg_step {l : ℕ} [Fact l.Prime] (c : Weil h →* Weil h')
    (hc : ∀ (σ : Weil h) z, (σ : G F Ω) z = (c σ : G M Ω) z) (hdeg : ∀ σ, deg (c σ) = deg σ)
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi : Continuous i) (hi' : Continuous i.symm)
    (hA : ∀ a, IsLocalArtin h a → ∃ a', IsLocalArtin h' a' ∧ ∀ σ, (a' (c σ) : w.adicCompletion M) = i (a σ))
    (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ)
    (hκ : ∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g')
    (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ)
    (hwt : ∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩) :
    IsLocAlg h' κ' wt' → IsLocAlg h κ wt := by
  rintro ⟨ph, hop, hph⟩
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hm : ∀ σ : Ine (F := F) A, ((c (ineIncl h σ) : Weil h') : G M Ω) ∈ Ine (F := M) A := fun σ => by
    rw [← deg_eq_zero_iff, hdeg, deg_ineIncl]
  let e : Ine (F := F) A →* Ine (F := M) A :=
    (((Weil h').subtype.comp c).comp (ineIncl h)).codRestrict _ hm
  have he : ∀ σ, ineIncl h' (e σ) = c (ineIncl h σ) := fun σ => Subtype.ext rfl
  refine ⟨ph.comp e, ?_, fun a ha σ => ?_⟩
  · obtain ⟨O', hO', hpre⟩ := isOpen_induced_iff.mp hop
    have h1 : (1 : G M Ω) ∈ O' := by
      have : (1 : Ine (F := M) A) ∈ Subtype.val ⁻¹' O' := by rw [hpre]; simp
      exact this
    obtain ⟨U, hU, hU1, hUO⟩ := GlobalTheory.WeilTransport.conj_nhds F Ω M Ω (RingEquiv.refl Ω) O' (hO'.mem_nhds h1)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset ((hU.preimage continuous_subtype_val).mem_nhds hU1) fun τ hτ => ?_)
    have hO : e τ ∈ Subtype.val ⁻¹' O' := hUO τ hτ _ (hc (ineIncl h τ))
    rw [hpre] at hO
    exact hO
  · obtain ⟨a', ha', haa⟩ := hA a ha
    have h1 := hph a' ha' (e σ)
    rw [hκ _ (Subgroup.inclusion (Weil_le_Dec h') (ineIncl h' (e σ))) (hc (ineIncl h σ)), MonoidHom.comp_apply, h1, he, haa]
    let E : Emb l w ≃ Emb l v :=
      { toFun := fun τ' => ⟨τ'.1.comp i.toRingHom, τ'.2.comp hi⟩
        invFun := fun τ => ⟨τ.1.comp i.symm.toRingHom, τ.2.comp hi'⟩
        left_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp)
        right_inv := fun τ => Subtype.ext (RingHom.ext fun x => by simp) }
    rw [← finprod_comp_equiv E]
    refine finprod_congr fun τ => ?_
    rw [hwt]
    rfl

private theorem artin_step (hG : GlobalArtinReciprocity) (c : Weil h' →* Weil h) (hcs : Function.Surjective c)
    (c' : Weil h →* Weil h') (hcc : ∀ σ, c' (c σ) = σ)
    (hsm : ∀ ξ : Weil h' →* ℂˣ, GlobalTheory.WeilDeligne.IsSmooth ξ → GlobalTheory.WeilDeligne.IsSmooth (ξ.comp c'))
    (i : v.adicCompletion F ≃+* w.adicCompletion M) (hi' : Continuous i.symm)
    (a : Weil h →* (v.adicCompletion F)ˣ) (ha : IsLocalArtin h a)
    (hglob : ∀ art', IsGlobalArtin art' → ∀ σ' : Weil h',
      art' (Neutral.B1.localIdele M w (Units.map i.toRingHom.toMonoidHom (a (c σ')))) = toAb M Ω σ') :
    IsLocalArtin h' ((Units.map i.toRingHom.toMonoidHom).comp (a.comp c)) := by
  obtain ⟨art, hart⟩ := hG M Ω
  obtain ⟨b, hs, ho, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art hart
  have hb : (Units.map i.toRingHom.toMonoidHom).comp (a.comp c) = b := MonoidHom.ext fun σ =>
    GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits' M Ω art hart w ((hglob art hart σ).trans (hg σ).symm)
  refine ⟨hb ▸ hs, hb ▸ GlobalTheory.ArtinInvCont.continuous_inv_on_ine M Ω A w h' art b hart ho hg, hb ▸ ho, fun ξ hξ => ?_, hglob⟩
  obtain ⟨χ, hχ, e⟩ := ha.factor _ (hsm ξ hξ)
  refine ⟨χ.comp (Units.map i.symm.toRingHom.toMonoidHom), IsOpen.preimage (Continuous.units_map _ hi') hχ, ?_⟩
  refine MonoidHom.ext fun σ => ?_
  have h1 : Units.map i.symm.toRingHom.toMonoidHom (Units.map i.toRingHom.toMonoidHom (a (c σ))) = a (c σ) := by
    ext; simp
  have h2 := DFunLike.congr_fun e (c σ)
  simp only [MonoidHom.comp_apply] at h2 ⊢
  rw [h1, ← h2, hcc]

end

theorem UpperTheory.isLocallyAlgebraic_transfer_of_placeIso :
    GlobalArtinReciprocity → ∀ {F M Ω : Type} [Field F] [NumberField F] [Field M] [NumberField M] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [Algebra M Ω] [IsAlgClosure M Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {v : Plc F} {w : Plc M} (h : IsPlaceOver A v) (h' : IsPlaceOver A w) (j : F →+* M) (i : v.adicCompletion F ≃+* w.adicCompletion M) (hP : PlaceIso A v A w (RingEquiv.refl Ω) j i) (κ : ↥(Dec (F := F) A) →* (Qbar l)ˣ) (κ' : ↥(Dec (F := M) A) →* (Qbar l)ˣ), (∀ (g : ↥(Dec (F := F) A)) (g' : ↥(Dec (F := M) A)), (∀ z, (g : G F Ω) z = (g' : G M Ω) z) → κ g = κ' g') → ∀ (wt : Emb l v → ℤ) (wt' : Emb l w → ℤ), (∀ τ' : Emb l w, wt' τ' = wt ⟨τ'.1.comp i.toRingHom, τ'.2.comp hP.cont⟩) → (IsLocAlg h κ wt ↔ IsLocAlg h' κ' wt') := by
  intro hG F M Ω _ _ _ _ _ _ _ _ _ l _ A v w h h' j i hP κ κ' hκ wt wt' hwt
  obtain ⟨c, hc, hdeg, -, hsm⟩ := GlobalTheory.WeilTransport.weil_equiv F Ω A v h M Ω A w h' _ j i hP
  have hi' : Continuous i.symm := by
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
    have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion M w
    exact i.toEquiv.continuous_symm_iff.2
      (AddMonoidHom.isOpenMap_of_sigmaCompact i.toAddEquiv.toAddMonoidHom i.surjective hP.cont)
  have hr : ∀ σ, WeilRel (RingEquiv.refl Ω) σ (c σ) := fun σ => (hc σ _).2 rfl
  have hr' : ∀ σ', WeilRel (RingEquiv.refl Ω) (c.symm σ') σ' := fun σ => (hc _ σ).2 (c.apply_symm_apply σ)
  have inj := GlobalTheory.T.globalArtin_localIdele_injective GlobalTheory.Published.chevalleyUnits'
  constructor
  · refine locAlg_step c.symm.toMonoidHom (fun σ z => (hr' σ z).symm)
      (fun σ => by rw [← hdeg]; simp) i.symm hi' hP.cont (fun a' ha' => ⟨_, artin_step hG c.toMonoidHom c.surjective
        c.symm.toMonoidHom c.symm_apply_apply (fun ξ hξ => (hsm _ _).2 ?_) i.symm hP.cont a' ha' fun art hart σ => ?_,
          fun σ => by simp⟩) κ' κ (fun g g' hg => (hκ g' g fun z => (hg z).symm).symm) wt' wt fun τ => ?_
    · convert hξ using 1
      ext; simp
    · obtain ⟨art', hart'⟩ := hG M Ω
      refine GlobalTheory.T.globalArtin_compat_localDegreeOne F Ω A v h M Ω A w h' _ j i hP art art' hart hart' σ (c σ) _ (hr σ) ?_
      rw [← ha'.glob art' hart' (c σ)]
      congr 2
      ext; simp
    · rw [hwt]
      congr 1
      exact Subtype.ext (RingHom.ext fun x => by simp)
  · refine locAlg_step c.toMonoidHom (fun σ z => hr σ z) hdeg i hP.cont hi'
      (fun a ha => ⟨_, artin_step hG c.symm.toMonoidHom c.symm.surjective
        c.toMonoidHom c.apply_symm_apply (fun ξ hξ => (hsm _ _).1 hξ) i hi' a ha fun art' hart' σ => ?_,
          fun σ => by simp⟩) κ κ' hκ wt wt' hwt
    obtain ⟨art, hart⟩ := hG F Ω
    obtain ⟨b, -, -, hg⟩ := GlobalTheory.InvLocalArtin.exists_invLocalArtin M Ω A w h' art' hart'
    have hx : Units.map i.toRingHom.toMonoidHom (Units.map i.symm.toRingHom.toMonoidHom (b σ)) = b σ := by
      ext; simp
    have h1 := GlobalTheory.T.globalArtin_compat_localDegreeOne F Ω A v h M Ω A w h' _ j i hP art art' hart hart' (c.symm σ) σ _ (hr' σ)
      (by rw [hx]; exact hg σ)
    have h2 := inj F Ω art hart v (h1.trans (ha.glob art hart (c.symm σ)).symm)
    rw [← hg σ, ← hx, h2]
    rfl
